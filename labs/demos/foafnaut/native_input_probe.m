// Optional desktop integration probe. It sends NSEvents only to its own window
// through NSApplication's queue; it does not synthesize global mouse input.
#import <Cocoa/Cocoa.h>
#include <stdint.h>
#include <stdio.h>
#include <math.h>

extern void *ng_create(uint32_t,uint32_t);
extern void *ng_window_handle(void);
extern void ng_pump(void);
extern int ng_next_event(void *);
extern void ng_hide(void);
extern void ng_set_title(const char *);
struct ProbeEvent { uint32_t type; int32_t a,b; uint32_t reserved; };
static unsigned checks;

static void discardTransport(void) {
  struct ProbeEvent event;
  while (ng_next_event(&event)) {}
}

static BOOL pointer(NSView *view,NSEventType type,NSPoint local,uint32_t kind) {
  NSWindow *window=view.window;
  NSPoint windowPoint=[view convertPoint:local toView:nil];
  NSEvent *event=[NSEvent mouseEventWithType:type location:windowPoint modifierFlags:0
    timestamp:NSProcessInfo.processInfo.systemUptime windowNumber:window.windowNumber
    context:nil eventNumber:checks+1 clickCount:1 pressure:type==NSEventTypeLeftMouseUp?0:1];
  [NSApp postEvent:event atStart:NO];
  ng_pump();
  // The NSWindow's display scale provides an independent expectation for the
  // untransformed content view. Do not reuse the production coordinate helper.
  int32_t x=(int32_t)floor(local.x*window.backingScaleFactor);
  int32_t y=(int32_t)floor(local.y*window.backingScaleFactor);
  struct ProbeEvent received;
  BOOL found=NO;
  while (ng_next_event(&received)) {
    if (received.type!=kind) continue;
    if (received.a!=x || received.b!=y) {
      fprintf(stderr,"FAIL Cocoa queue kind=%u: received (%d,%d), expected (%d,%d)\n",
        kind,received.a,received.b,x,y);
      return NO;
    }
    found=YES;
  }
  if (!found) {
    fprintf(stderr,"FAIL Cocoa queue did not deliver pointer kind=%u; key=%d active=%d\n",
      kind,window.keyWindow,NSApp.active);
    return NO;
  }
  checks++;
  return YES;
}

static BOOL gesture(NSView *view,NSPoint start,NSPoint end) {
  return pointer(view,NSEventTypeLeftMouseDown,start,2) &&
    pointer(view,NSEventTypeLeftMouseDragged,end,3) &&
    pointer(view,NSEventTypeLeftMouseUp,end,4);
}

int main(void) {
  @autoreleasepool {
    [NSApplication sharedApplication];
    if (NSScreen.screens.count==0) {
      fprintf(stderr,"UNAVAILABLE: Cocoa input probe needs a desktop WindowServer session.\n");
      return 77;
    }
    NSView *view=(__bridge NSView *)ng_create(768,512);
    if (!view || !ng_window_handle()) {
      fprintf(stderr,"FAIL native window/view creation\n");
      return 1;
    }
    ng_set_title("Native input integration check — closes automatically");
    // Pump briefly for activation, without entering NSApplication.run (the
    // production host uses this same explicit pump).
    for (unsigned i=0;i<20;i++) {
      ng_pump();
      if (view.window.keyWindow && NSApp.active) break;
      [NSThread sleepForTimeInterval:0.01];
    }
    discardTransport();
    BOOL ok=gesture(view,NSMakePoint(208.25,208.25),NSMakePoint(280.25,230.25)) &&
      gesture(view,NSMakePoint(188.25,64.25),NSMakePoint(240.25,80.25)) &&
      gesture(view,NSMakePoint(12.25,12.25),NSMakePoint(740.25,490.25));
    if (ok) {
      [view.window setContentSize:NSMakeSize(467,445)];
      ng_pump();discardTransport();
      ok=gesture(view,NSMakePoint(350.25,328.25),NSMakePoint(100.25,100.25));
    }
    ng_hide();
    if (!ok) return 1;
    printf("Cocoa queue → native event transport: %u pointer checks passed at %.1fx.\n",
      checks,view.window.backingScaleFactor);
    printf("Synthetic per-window events only; GPU rendering and physical pointer delivery are separate checks.\n");
    return 0;
  }
}
