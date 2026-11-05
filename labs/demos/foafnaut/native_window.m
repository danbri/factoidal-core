// macOS transport only: NSWindow/NSView lifetime and native event forwarding.
// No geometry, widget state, animation policy, or GPU drawing lives here.
#import <Cocoa/Cocoa.h>
#import <QuartzCore/CAMetalLayer.h>
#import <QuartzCore/CATransaction.h>
#include <pthread.h>
#include <stdint.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "native_coordinates.h"

struct NGEvent { uint32_t type; int32_t a; int32_t b; uint32_t reserved; };
static struct NGEvent events[256];
static uint32_t eventCount;
static NSWindow *window;
static NSView *content;
static id delegate;
static int traceInput;
static int rawMoveTraced,viewMoveTraced;
static NSPoint framebufferPoint(NSView *view,NSPoint local) {
  NSRect bounds=view.bounds;
  NSSize backing=[view convertRectToBacking:bounds].size;
  NGPoint point=ng_framebuffer_point((NGPoint){local.x,local.y},
    (NGPoint){bounds.origin.x,bounds.origin.y},
    (NGPoint){bounds.size.width,bounds.size.height},(NGPoint){backing.width,backing.height});
  return NSMakePoint(point.x,point.y);
}
static void tracePointer(const char *stage,NSEvent *event,uint32_t type,int *moveTraced) {
  if(!traceInput)return;
  if(type==2)*moveTraced=0;
  if(type==3){
    if(event.type!=NSEventTypeLeftMouseDragged || *moveTraced)return;
    *moveTraced=1;
  }
  NSPoint raw=event.locationInWindow;
  NSPoint local=[content convertPoint:raw fromView:nil];
  NSPoint backing=framebufferPoint(content,local);
  NSPoint cocoaBacking=[content convertPointToBacking:local];
  fprintf(stderr,"Input Cocoa %s kind=%u window=(%.1f,%.1f) local=(%.1f,%.1f) backing=(%.1f,%.1f) cocoaBacking=(%.1f,%.1f) key=%d active=%d firstResponder=%d bounds=(%.1f,%.1f) scale=%.1f\n",
    stage,type,raw.x,raw.y,local.x,local.y,backing.x,backing.y,cocoaBacking.x,cocoaBacking.y,
    window.keyWindow,NSApp.active,window.firstResponder==content,
    content.bounds.size.width,content.bounds.size.height,window.backingScaleFactor);
}
static int canPresent(void) {
  return pthread_main_np() && window && content && window.visible && !window.miniaturized &&
    content.window==window && !content.hiddenOrHasHiddenAncestor &&
    (window.occlusionState&NSWindowOcclusionStateVisible)!=0;
}

static void enqueue(uint32_t type, int32_t a, int32_t b) {
  // Adjacent move/resize events are coalesced; discrete events remain ordered.
  if (eventCount && (type == 1 || type == 3) && events[eventCount-1].type == type) {
    events[eventCount-1] = (struct NGEvent){type,a,b,0}; return;
  }
  if (eventCount == 256) {
    // Bounded transport queue. A pathological flood drops the oldest event.
    memmove(events, events+1, 255*sizeof(struct NGEvent)); eventCount--;
  }
  events[eventCount++] = (struct NGEvent){type,a,b,0};
}
static void resizeEvent(void) {
  if (!content) return;
  NSRect rect = [content convertRectToBacking:content.bounds];
  content.layer.contentsScale = window.backingScaleFactor;
  enqueue(1, (int32_t)llround(rect.size.width), (int32_t)llround(rect.size.height));
}

@interface NGView : NSView
@end
@implementation NGView
- (BOOL)isFlipped { return YES; }
- (BOOL)acceptsFirstResponder { return YES; }
- (BOOL)acceptsFirstMouse:(NSEvent *)event { (void)event; return YES; }
- (void)sendPointer:(NSEvent *)event type:(uint32_t)type {
  tracePointer("view",event,type,&viewMoveTraced);
  NSPoint point = [self convertPoint:event.locationInWindow fromView:nil];
  point = framebufferPoint(self,point);
  enqueue(type, (int32_t)floor(point.x), (int32_t)floor(point.y));
}
- (void)mouseDown:(NSEvent *)event { [self sendPointer:event type:2]; }
- (void)mouseMoved:(NSEvent *)event { [self sendPointer:event type:3]; }
- (void)mouseDragged:(NSEvent *)event { [self sendPointer:event type:3]; }
- (void)mouseUp:(NSEvent *)event { [self sendPointer:event type:4]; }
- (void)keyDown:(NSEvent *)event {
  NSEventModifierFlags flags=event.modifierFlags;
  int32_t modifiers=((flags&NSEventModifierFlagShift)?1:0) |
    ((flags&NSEventModifierFlagCommand)?2:0) |
    ((flags&NSEventModifierFlagOption)?4:0) |
    ((flags&NSEventModifierFlagControl)?8:0);
  enqueue(5,event.keyCode,modifiers);
  // AppKit resolves keyboard layouts/dead keys into committed text. Lean
  // receives special keys separately and owns all editing and shortcuts.
  if (!(flags&(NSEventModifierFlagCommand|NSEventModifierFlagControl)))
    [self interpretKeyEvents:@[event]];
}
- (void)insertText:(id)value { [self insertText:value replacementRange:NSMakeRange(NSNotFound,0)]; }
- (void)insertText:(id)value replacementRange:(NSRange)range {
  (void)range;
  NSString *text=[value isKindOfClass:[NSAttributedString class]] ? [value string] : value;
  NSData *scalars=[text dataUsingEncoding:NSUTF32LittleEndianStringEncoding];
  const uint32_t *chars=scalars.bytes;
  for (NSUInteger i=0;i<scalars.length/4;i++) enqueue(9,(int32_t)chars[i],0);
}
- (void)doCommandBySelector:(SEL)selector { (void)selector; /* key event already sent to Lean */ }
@end

@interface NGDelegate : NSObject <NSWindowDelegate, NSApplicationDelegate>
@end
@implementation NGDelegate
- (BOOL)windowShouldClose:(NSWindow *)sender { (void)sender; enqueue(6,0,0); return NO; }
- (void)windowDidResize:(NSNotification *)note { (void)note; resizeEvent(); }
- (void)windowDidChangeBackingProperties:(NSNotification *)note { (void)note; resizeEvent(); }
- (void)windowDidResignKey:(NSNotification *)note { (void)note; enqueue(4,0,0); }
- (void)windowDidChangeOcclusionState:(NSNotification *)note { (void)note; enqueue(8,canPresent(),0); }
- (NSApplicationTerminateReply)applicationShouldTerminate:(NSApplication *)sender {
  (void)sender; enqueue(6,0,0); return NSTerminateCancel;
}
@end

int ng_is_main_thread(void) { return pthread_main_np(); }
void ng_set_content_size(uint32_t width, uint32_t height) {
  if (!pthread_main_np() || !window) return;
  @autoreleasepool { [window setContentSize:NSMakeSize(width,height)]; }
}
void ng_set_input_trace(int enabled) { traceInput=enabled;rawMoveTraced=0;viewMoveTraced=0; }
int ng_can_present(void) { return canPresent(); }
void ng_show_after_surface(void) {
  if (!pthread_main_np()) return;
  @autoreleasepool {
    // UnsafeWindowSurface can request pathless FFI permission from Terminal,
    // obscuring our window. Restore focus once after that constructor returns.
    [window makeKeyAndOrderFront:nil];
    [NSApp activateIgnoringOtherApps:YES];
    [NSApp updateWindows];
    [CATransaction flush];
  }
}
void ng_prepare_surface(void) {
  if (!pthread_main_np()) return;
  @autoreleasepool {
    [content layoutSubtreeIfNeeded];
    // This host pumps AppKit manually rather than running NSApplication.run.
    // Apple requires an explicit flush when there is no native runloop commit.
    [CATransaction flush];
  }
}
void ng_surface_state(double *out) {
  memset(out,0,18*sizeof(double));
  out[0]=pthread_main_np();
  if (!out[0] || !window || !content) return;
  @autoreleasepool {
    out[1]=window.visible;
    out[2]=window.miniaturized;
    out[3]=content.window==window;
    out[4]=[content.layer isKindOfClass:[CAMetalLayer class]];
    out[5]=content.bounds.size.width; out[6]=content.bounds.size.height;
    NSRect backing=[content convertRectToBacking:content.bounds];
    out[7]=backing.size.width; out[8]=backing.size.height;
    out[9]=content.layer.contentsScale;
    out[10]=content.layer.bounds.size.width; out[11]=content.layer.bounds.size.height;
    if (out[4]) {
      CAMetalLayer *layer=(CAMetalLayer *)content.layer;
      out[12]=layer.drawableSize.width; out[13]=layer.drawableSize.height;
      out[14]=layer.device!=nil;
    }
    out[15]=(window.occlusionState&NSWindowOcclusionStateVisible)!=0;
    out[16]=NSApp.running;
    out[17]=content.hiddenOrHasHiddenAncestor;
  }
}
void *ng_window_handle(void) {
  if (!pthread_main_np()) return NULL;
  return (__bridge void *)window;
}
void ng_set_title(const char *title) {
  if (!pthread_main_np()) return;
  @autoreleasepool { window.title = [NSString stringWithUTF8String:title] ?: @"Lean native demo"; }
}
// Clipboard requests are explicit effects from Lean. Returned text is a
// UTF-8 snapshot owned by the caller until ng_free; no selection state here.
char *ng_clipboard_copy(void) {
  if (!pthread_main_np()) return NULL;
  @autoreleasepool {
    NSString *text=[[NSPasteboard generalPasteboard] stringForType:NSPasteboardTypeString] ?: @"";
    NSData *bytes=[text dataUsingEncoding:NSUTF8StringEncoding];
    if (!bytes || bytes.length>1048576) return NULL;
    char *copy=malloc(bytes.length+1);
    if (!copy) return NULL;
    memcpy(copy,bytes.bytes,bytes.length); copy[bytes.length]=0;
    return copy;
  }
}
void ng_free(void *pointer) { free(pointer); }
int ng_clipboard_write(const char *text) {
  if (!pthread_main_np() || !text) return 0;
  @autoreleasepool {
    NSString *value=[NSString stringWithUTF8String:text];
    if (!value) return 0;
    NSPasteboard *board=[NSPasteboard generalPasteboard];
    [board clearContents];
    return [board setString:value forType:NSPasteboardTypeString] ? 1 : 0;
  }
}
// The standard menu. Quit reaches applicationShouldTerminate, which sends the host
// a close event, and Close goes through windowShouldClose. Page keys stay with Lean.
static void installMenu(void) {
  NSString *name=NSProcessInfo.processInfo.processName;
  NSMenu *bar=[[NSMenu alloc] init];
  NSMenuItem *appItem=[bar addItemWithTitle:name action:nil keyEquivalent:@""];
  NSMenu *appMenu=[[NSMenu alloc] initWithTitle:name];
  [appMenu addItemWithTitle:[@"Hide " stringByAppendingString:name] action:@selector(hide:) keyEquivalent:@"h"];
  [appMenu addItem:[NSMenuItem separatorItem]];
  [appMenu addItemWithTitle:[@"Quit " stringByAppendingString:name] action:@selector(terminate:) keyEquivalent:@"q"];
  appItem.submenu=appMenu;
  NSMenuItem *windowItem=[bar addItemWithTitle:@"Window" action:nil keyEquivalent:@""];
  NSMenu *windowMenu=[[NSMenu alloc] initWithTitle:@"Window"];
  [windowMenu addItemWithTitle:@"Minimize" action:@selector(performMiniaturize:) keyEquivalent:@"m"];
  [windowMenu addItemWithTitle:@"Close" action:@selector(performClose:) keyEquivalent:@"w"];
  windowItem.submenu=windowMenu;
  NSApp.mainMenu=bar;
  NSApp.windowsMenu=windowMenu;
}
void *ng_create(uint32_t width, uint32_t height) {
  if (!pthread_main_np() || window) return NULL;
  @autoreleasepool {
    [NSApplication sharedApplication];
    [NSApp setActivationPolicy:NSApplicationActivationPolicyRegular];
    delegate = [[NGDelegate alloc] init];
    NSApp.delegate = delegate;
    installMenu();
    window = [[NSWindow alloc] initWithContentRect:NSMakeRect(0,0,width,height)
      styleMask:NSWindowStyleMaskTitled|NSWindowStyleMaskClosable|NSWindowStyleMaskMiniaturizable|NSWindowStyleMaskResizable
      backing:NSBackingStoreBuffered defer:NO];
    window.releasedWhenClosed = NO;
    window.title = @"Lean WASM + raw WebGPU — drag circle / pink handle; Space animate; Esc close";
    window.contentMinSize = NSMakeSize(192,128);
    window.contentMaxSize = NSMakeSize(2048,2048);
    window.acceptsMouseMovedEvents = YES;
    window.delegate = delegate;
    content = [[NGView alloc] initWithFrame:NSMakeRect(0,0,width,height)];
    content.wantsLayer = YES;
    content.layer = [CAMetalLayer layer];
    // Keep the drawn frame at its size during a resize; the default gravity
    // scales the old image until the next frame.
    content.layer.contentsGravity = kCAGravityTopLeft;
    window.contentView = content;
    [window makeFirstResponder:content];
    [window center];
    [window makeKeyAndOrderFront:nil];
    [NSApp finishLaunching];
    [NSApp activateIgnoringOtherApps:YES];
    resizeEvent();
    [NSApp updateWindows];
    [CATransaction flush];
    return (__bridge void *)content;
  }
}
// Window edge drag, done here so JS keeps running. In [NSApp sendEvent:] AppKit
// tracks a resize in its own loop until the mouse is up, and this host only runs
// JS between pumps, so Lean could not lay out the page during the drag.
static int resizeEdges; // 1 left, 2 right, 4 bottom
static NSPoint resizeMouse;
static NSRect resizeFrame;
static int beginEdgeResize(NSEvent *event) {
  if (event.type!=NSEventTypeLeftMouseDown) return 0;
  NSPoint p=[NSEvent mouseLocation];
  NSRect f=window.frame;
  if (traceInput) fprintf(stderr,"native mouse down at %.1f,%.1f; window %.1f,%.1f %.1fx%.1f; event window %s\n",
    p.x,p.y,f.origin.x,f.origin.y,f.size.width,f.size.height,event.window==window?"ours":"other");
  if (event.window!=window) return 0;
  CGFloat m=5;
  if (p.y>NSMaxY(f)-m || p.x<NSMinX(f)-m || p.x>NSMaxX(f)+m || p.y<NSMinY(f)-m) return 0;
  int edges=(p.x<NSMinX(f)+m?1:0)|(p.x>NSMaxX(f)-m?2:0)|(p.y<NSMinY(f)+m?4:0);
  if (!edges) return 0;
  resizeEdges=edges; resizeMouse=p; resizeFrame=f;
  if (traceInput) fprintf(stderr,"native edge resize begins, edges %d\n",edges);
  return 1;
}
static int continueEdgeResize(NSEvent *event) {
  if (!resizeEdges) return 0;
  if (event.type==NSEventTypeLeftMouseUp) { resizeEdges=0; return 1; }
  if (event.type!=NSEventTypeLeftMouseDragged) return 0;
  NSPoint p=[NSEvent mouseLocation];
  CGFloat dx=p.x-resizeMouse.x, dy=p.y-resizeMouse.y;
  NSRect f=resizeFrame;
  NSSize least=[window frameRectForContentRect:NSMakeRect(0,0,window.contentMinSize.width,window.contentMinSize.height)].size;
  NSSize most=[window frameRectForContentRect:NSMakeRect(0,0,window.contentMaxSize.width,window.contentMaxSize.height)].size;
  if (resizeEdges&2) f.size.width=MIN(MAX(resizeFrame.size.width+dx,least.width),most.width);
  if (resizeEdges&1) {
    f.size.width=MIN(MAX(resizeFrame.size.width-dx,least.width),most.width);
    f.origin.x=NSMaxX(resizeFrame)-f.size.width;
  }
  if (resizeEdges&4) {
    f.size.height=MIN(MAX(resizeFrame.size.height-dy,least.height),most.height);
    f.origin.y=NSMaxY(resizeFrame)-f.size.height;
  }
  [window setFrame:f display:NO];
  return 1;
}
void ng_pump(void) {
  if (!pthread_main_np()) return;
  @autoreleasepool {
    NSEvent *event;
    // Bound each pump so the JS event loop can submit frames under input floods.
    for (int i=0; i<256; i++) {
      event = [NSApp nextEventMatchingMask:NSEventMaskAny untilDate:[NSDate distantPast]
        inMode:NSDefaultRunLoopMode dequeue:YES];
      if (!event) break;
      if(traceInput) {
        if(event.type==NSEventTypeLeftMouseDown)tracePointer("raw",event,2,&rawMoveTraced);
        else if(event.type==NSEventTypeLeftMouseUp)tracePointer("raw",event,4,&rawMoveTraced);
        else if(event.type==NSEventTypeLeftMouseDragged)tracePointer("raw",event,3,&rawMoveTraced);
      }
      if (continueEdgeResize(event) || beginEdgeResize(event)) continue;
      [NSApp sendEvent:event];
    }
    [NSApp updateWindows];
    [CATransaction flush];
  }
}
int ng_next_event(void *out) {
  if (!pthread_main_np() || !eventCount) return 0;
  memcpy(out, events, sizeof(struct NGEvent));
  memmove(events, events+1, (--eventCount)*sizeof(struct NGEvent));
  return 1;
}
void ng_hide(void) {
  if (!pthread_main_np()) return;
  @autoreleasepool { [window orderOut:nil]; }
  // Retain window/view and loaded dylib until process exit: the WebGPU surface
  // holds their native handles. Never free NSView underneath that surface.
}
