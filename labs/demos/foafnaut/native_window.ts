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
    // Optional, so an older window library still opens.
    ng_events_dropped: { parameters: [], result: "u32", optional: true },
    ng_event_clock: { parameters: [], result: "u32", optional: true },
    ng_hide: { parameters: [], result: "void" },
    ng_set_title: { parameters: ["buffer"], result: "void" },
    ng_prepare_surface: { parameters: [], result: "void" },
    ng_surface_state: { parameters: ["buffer"], result: "void" },
    ng_can_present: { parameters: [], result: "i32" },
    ng_show_after_surface: { parameters: [], result: "void" },
    ng_set_input_trace: { parameters: ["i32"], result: "void" },
    ng_set_content_size: { parameters: ["u32","u32"], result: "void" },
    ng_test_raise: { parameters: [], result: "void" },
    ng_set_history: { parameters: ["i32","i32"], result: "void" },
    ng_test_key: { parameters: ["buffer","i32"], result: "i32" },
    ng_test_event: { parameters: ["u32","i32","i32"], result: "void" },
    ng_clipboard_copy: { parameters: [], result: "pointer" },
    ng_free: { parameters: ["pointer"], result: "void" },
    ng_clipboard_write: { parameters: ["buffer"], result: "i32" },
    ng_open_url: { parameters: ["buffer"], result: "i32" },
    ng_set_cursor: { parameters: ["i32"], result: "void", optional: true },
    ng_app_start: { parameters: [], result: "void", optional: true },
    ng_app_state: { parameters: ["buffer"], result: "void", optional: true },
    ng_print_paper: { parameters: ["buffer"], result: "void", optional: true },
    ng_print: { parameters: ["buffer","u32","u32","u32","f64","f64","buffer","buffer"], result: "i32", optional: true },
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
    readClipboard() {
      const pointer=symbols.ng_clipboard_copy();
      if(!pointer)throw new Error("Clipboard text unavailable or exceeds the 1 MiB transport limit");
      try { return new Deno.UnsafePointerView(pointer).getCString(); }
      finally { symbols.ng_free(pointer); }
    },
    // Lean chose this URL. The operating system's default browser opens it.
    openURL(url:string) {
      if(url.includes("\0")||!symbols.ng_open_url(new TextEncoder().encode(url+"\0")))throw new Error("The system browser did not open the URL");
    },
    writeClipboard(text:string) {
      if(text.includes("\0"))throw new Error("Clipboard text contains NUL");
      if(!symbols.ng_clipboard_write(new TextEncoder().encode(text+"\0")))
        throw new Error("Native clipboard write failed");
    },
    // Lean chose the pointer; an older window library keeps the arrow.
    setCursor:(kind:string)=>symbols.ng_set_cursor?.(kind==="hand"?1:kind==="text"?2:0),
    setHistory:(back:boolean,forward:boolean)=>symbols.ng_set_history(back?1:0,forward?1:0),
    // A regular app in the Dock and Command-Tab, with its menu, before the engine loads.
    appStart:()=>symbols.ng_app_start?.(),
    appState() {
      const state=new Int32Array(3);symbols.ng_app_state?.(state);
      return {regular:state[0]===1,active:state[1]===1,keyWindow:state[2]===1};
    },
    // The paper of the page setup, in points; null with an older window library.
    printPaper() {
      if(!symbols.ng_print_paper)return null;
      const state=new Float64Array(6);symbols.ng_print_paper(state);
      return {width:state[0],height:state[1],left:state[2],right:state[3],top:state[4],bottom:state[5]};
    },
    // Page images Lean drew, to the system print operation. With pdfPath, saved there with no panel.
    print(pages:Uint8Array,count:number,width:number,height:number,pointWidth:number,pointHeight:number,title:string,pdfPath?:string) {
      if(!symbols.ng_print)throw new Error("This window library can not print");
      const encoder=new TextEncoder();
      return symbols.ng_print(pages,count,width,height,pointWidth,pointHeight,encoder.encode(title.replaceAll("\0","")+"\0"),encoder.encode((pdfPath??"")+"\0"));
    },
    testRaise:()=>symbols.ng_test_raise(),
    testKey:(key:string,shift=false)=>symbols.ng_test_key(new TextEncoder().encode(key+"\0"),shift?1:0)===1,
    testEvent:(kind:number,a:number,b:number)=>symbols.ng_test_event(kind,a,b),
    setInputTrace:(enabled:boolean)=>symbols.ng_set_input_trace(enabled?1:0),
    setContentSize:(width:number,height:number)=>symbols.ng_set_content_size(width,height),
    create(width: number, height: number, title?:string) {
      const pointer = symbols.ng_create(width,height);
      if (!pointer) throw new Error("Native NSView creation failed or was called off the main thread");
      const windowHandle=symbols.ng_window_handle();
      if (!windowHandle) throw new Error("Native NSWindow handle is unavailable");
      if (title) symbols.ng_set_title(new TextEncoder().encode(title+"\0"));
      return {windowHandle,displayHandle:pointer};
    },
    setTitle:(title:string)=>symbols.ng_set_title(new TextEncoder().encode(title+"\0")),
    pump() {
      if (!isMainThread()) throw new Error("Native event pump moved off main thread");
      symbols.ng_pump();
    },
    next(): UIEvent | null {
      return symbols.ng_next_event(buffer) ? { kind:view.getUint32(0,true), a:view.getInt32(4,true), b:view.getInt32(8,true), time:view.getUint32(12,true) } : null;
    },
    // Milliseconds on the clock of event.time; null with an older window library.
    eventClock(): number | null { return symbols.ng_event_clock ? symbols.ng_event_clock() : null; },
    eventsDropped(): number { return symbols.ng_events_dropped ? symbols.ng_events_dropped() : 0;
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
