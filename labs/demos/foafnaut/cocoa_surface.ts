// Deno 2.9.4 ext/canvas/byow.rs rejects a null window_handle before its
// Cocoa branch uses display_handle as NSView*. Supply both real native objects.
export type CocoaHandles<P> = { windowHandle:P|null; displayHandle:P|null };
export function cocoaSurfaceOptions<P>(handles:CocoaHandles<P>,width:number,height:number) {
  if (!handles.windowHandle || !handles.displayHandle) {
    throw new Error("Native surface requires both a real NSWindow and NSView handle");
  }
  if (![width,height].every(n=>Number.isInteger(n)&&n>0)) throw new Error("Invalid native surface dimensions");
  return {system:"cocoa" as const,windowHandle:handles.windowHandle,displayHandle:handles.displayHandle,width,height};
}
