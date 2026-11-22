// The serif face (owner decision 2026-11-16): `serif`, and the initial font-family, draw
// with Liberation Serif (third_party/fonts/liberation-serif, OFL 1.1, metric-compatible
// with Times New Roman), as browsers draw them with a Times-like face. Lean decides which
// text is serif (FontFaceRule.genericOf). The window (run_html.ts) gives the face to the
// engine that lays pages out (fontLoad mode 3) once a session, before the first page, so the
// first layout of a serif page is final (WebDocument.serifWanted_held); the engine uses it
// only for a page whose cascade has serif text, so other pages lay out as before. A render
// whose text wants the face while the engine holds none (the load failed) answers
// `wantsSerif` (WebDocument.withWants).

//
// The monospace face is given the same way (fontLoad mode 4, WebDocument.loadMonoFont): text
// whose family resolves to `monospace` (FontFaceRule.genericOf: `monospace`, `ui-monospace`,
// Courier New, Menlo, Consolas, ...; the UA sheet gives it to pre, code, kbd, samp, tt) draws
// with Liberation Mono (third_party/fonts/liberation-mono, OFL 1.1, the advance widths of
// Courier New), and a render whose text wants it while the engine holds none answers
// `wantsMono`.

/** The family the engine holds the face by. */
export const SERIF_FAMILY="Liberation Serif";
/** The file of the face, beside the other bundled fonts (also in the compiled app). */
export const serifFontPath=()=>decodeURIComponent(new URL("../../../third_party/fonts/liberation-serif/LiberationSerif-Regular.ttf",import.meta.url).pathname);
/** Whether a render answer says that its text wants the serif face. */
export const wantsSerif=(answer:unknown)=>(answer as {wantsSerif?:unknown}|undefined)?.wantsSerif===true;
/** The family the engine holds the monospace face by. */
export const MONO_FAMILY="Liberation Mono";
/** The file of the monospace face. */
export const monoFontPath=()=>decodeURIComponent(new URL("../../../third_party/fonts/liberation-mono/LiberationMono-Regular.ttf",import.meta.url).pathname);
/** Whether a render answer says that its text wants the monospace face. */
export const wantsMono=(answer:unknown)=>(answer as {wantsMono?:unknown}|undefined)?.wantsMono===true;

/** Gives a face once: `want()` starts the load the first time and answers whether it went in;
later calls answer undefined (the face is held, or on its way). `load` puts the face into the
engine; a failure is said once, and the text stays in the first font. `name` names the face in
that message. */
export function serifFontHost(load:()=>Promise<unknown>,name="serif") {
  let loading:Promise<boolean>|undefined;
  const stats={wanted:0,loads:0,failures:0};
  return {
    stats,
    /** The face was asked for (and is held, or on its way, or failed). */
    get started(){return loading!==undefined;},
    want():Promise<boolean>|undefined {
      stats.wanted++;
      if(loading)return undefined;
      stats.loads++;
      loading=load().then(()=>true,error=>{
        stats.failures++;
        console.error(`Native HTML: no ${name} face, ${name} text stays in the first font:`,String(error instanceof Error?error.message:error));
        return false;
      });
      return loading;
    },
  };
}
