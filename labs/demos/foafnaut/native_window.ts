import type { UIEvent } from "./ui_engine.ts";

export function libraryPath(): string {
  return Deno.build.standalone
    ? Deno.execPath().slice(0, Deno.execPath().lastIndexOf("/") + 1) + "libnative-window.dylib"
    : decodeURIComponent(new URL("./.build/native/libnative-window.dylib", import.meta.url).pathname);
}

export function loadNativeWindow() {
  if (Deno.build.os !== "darwin") throw new Error("This native window shim currently supports macOS only");
  const library = Deno.dlopen(libraryPath(), {
    ng_is_main_thread: { parameters: [], result: "i32" },
    ng_create: { parameters: ["u32","u32"], result: "pointer" },
    ng_window_handle: { parameters: [], result: "pointer" },
    ng_pump: { parameters: [], result: "void" },
    ng_next_event: { parameters: ["buffer"], result: "i32" },
    ng_hide: { parameters: [], result: "void" },
    ng_set_title: { parameters: ["buffer"], result: "void" },
    ng_prepare_surface: { parameters: [], result: "void" },
    ng_surface_state: { parameters: ["buffer"], result: "void" },
    ng_can_present: { parameters: [], result: "i32" },
    ng_show_after_surface: { parameters: [], result: "void" },
    ng_set_input_trace: { parameters: ["i32"], result: "void" },
  } as const);
  const symbols = library.symbols;
  const isMainThread = () => symbols.ng_is_main_thread() === 1;
  if (!isMainThread()) {
    library.close();
    throw new Error("Cocoa/WebGPU must run on the OS main thread; workers and nonblocking FFI are unsupported");
  }
  const buffer = new Uint8Array(16);
  const view = new DataView(buffer.buffer);
  return {
    isMainThread,
    setInputTrace:(enabled:boolean)=>symbols.ng_set_input_trace(enabled?1:0),
    create(width: number, height: number, title?:string) {
      const pointer = symbols.ng_create(width,height);
      if (!pointer) throw new Error("Native NSView creation failed or was called off the main thread");
      const windowHandle=symbols.ng_window_handle();
      if (!windowHandle) throw new Error("Native NSWindow handle is unavailable");
      if (title) symbols.ng_set_title(new TextEncoder().encode(title+"\0"));
      return {windowHandle,displayHandle:pointer};
    },
    pump() {
      if (!isMainThread()) throw new Error("Native event pump moved off main thread");
      symbols.ng_pump();
    },
    next(): UIEvent | null {
      return symbols.ng_next_event(buffer) ? { kind:view.getUint32(0,true), a:view.getInt32(4,true), b:view.getInt32(8,true) } : null;
    },
    hide: () => symbols.ng_hide(),
    prepareSurface: () => symbols.ng_prepare_surface(),
    canPresent: () => symbols.ng_can_present()===1,
    showAfterSurface: () => symbols.ng_show_after_surface(),
    surfaceState() {
      const state=new Float64Array(18);
      symbols.ng_surface_state(state);
      return {
        mainThread:!!state[0],visible:!!state[1],miniaturized:!!state[2],attached:!!state[3],metalLayer:!!state[4],
        viewSize:[state[5],state[6]],backingSize:[state[7],state[8]],contentsScale:state[9],
        layerBounds:[state[10],state[11]],drawableSize:[state[12],state[13]],hasMetalDevice:!!state[14],
        occlusionVisible:!!state[15],nativeRunloop:!!state[16],hiddenAncestor:!!state[17],
      };
    },
    // Keep the library and NSView alive until process exit; no dlclose under GPU.
  };
}
