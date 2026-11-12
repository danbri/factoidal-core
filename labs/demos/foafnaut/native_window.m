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
// A growing FIFO. Clicks, keys and other discrete events are never dropped.
static struct NGEvent *events;
static uint32_t eventHead, eventCount, eventCapacity, eventsDropped;
static double eventEpoch;
static NSWindow *window;
static NSView *content;
static id delegate;
static int traceInput;
// Off-screen mode (issue 1268): the window is made but never shown, so the event queue,
// the menu key matching and printing work with the screen locked or with no display. The
// host draws into a GPU texture. The backing scale is fixed, so sweeps see the same sizes
// on every machine; the clipboard is a private pasteboard, not the person's.
static double offscreenScale;
static NSPasteboard *pasteboard(void) {
  static NSPasteboard *own;
  if (offscreenScale<=0) return [NSPasteboard generalPasteboard];
  if (!own) own=[NSPasteboard pasteboardWithUniqueName];
  return own;
}
static int rawMoveTraced,viewMoveTraced;
static NSSize backingSize(NSView *view) {
  if (offscreenScale>0) return NSMakeSize(view.bounds.size.width*offscreenScale,view.bounds.size.height*offscreenScale);
  return [view convertRectToBacking:view.bounds].size;
}
static NSPoint framebufferPoint(NSView *view,NSPoint local) {
  NSRect bounds=view.bounds;
  NSSize backing=backingSize(view);
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

static uint32_t eventTime(void) {
  // Milliseconds since the first event, so the host can measure input latency.
  double now = CACurrentMediaTime();
  if (eventEpoch == 0) eventEpoch = now;
  return (uint32_t)llround((now - eventEpoch) * 1000.0);
}
static void enqueue(uint32_t type, int32_t a, int32_t b) {
  uint32_t time = eventTime();
  if (eventCount) {
    struct NGEvent *last = &events[eventHead + eventCount - 1];
    // Adjacent moves and resizes keep only the newest position; adjacent scrolls add up.
    // The time stays that of the first event, so latency counts from it.
    if ((type == 1 || type == 3) && last->type == type) { last->a = a; last->b = b; return; }
    if (type == 11 && last->type == 11) { last->a += a; return; }
    if (type == 12 && last->type == 12 && last->b == b) { last->a += a; return; }
  }
  if (eventHead + eventCount == eventCapacity) {
    if (eventHead) { memmove(events, events + eventHead, eventCount * sizeof(struct NGEvent)); eventHead = 0; }
    if (eventCount == eventCapacity) {
      // 1 MiB of events is far above any person's input; past it, count and refuse.
      if (eventCapacity >= 65536) { eventsDropped++; return; }
      uint32_t capacity = eventCapacity ? eventCapacity * 2 : 256;
      struct NGEvent *grown = realloc(events, capacity * sizeof(struct NGEvent));
      if (!grown) { eventsDropped++; return; }
      events = grown; eventCapacity = capacity;
    }
  }
  events[eventHead + eventCount++] = (struct NGEvent){type, a, b, time};
}
uint32_t ng_events_dropped(void) { return eventsDropped; }
uint32_t ng_event_clock(void) { return eventTime(); }
static void resizeEvent(void) {
  if (!content) return;
  NSSize size = backingSize(content);
  content.layer.contentsScale = offscreenScale>0 ? offscreenScale : window.backingScaleFactor;
  enqueue(1, (int32_t)llround(size.width), (int32_t)llround(size.height));
}

// The pointer Lean chose: 0 arrow, 1 pointing hand, 2 I-beam. The host sends it only when it changes.
static int cursorKind;
static int hoverEdges, resizeEdges; // window edges under the pointer, and of a resize drag
static NSCursor *shownCursor(void) {
  return cursorKind==1 ? NSCursor.pointingHandCursor : cursorKind==2 ? NSCursor.IBeamCursor : NSCursor.arrowCursor;
}
void ng_set_cursor(int kind) {
  if (!pthread_main_np() || kind<0 || kind>2 || kind==cursorKind) return;
  cursorKind=kind;
  if (!hoverEdges && !resizeEdges) [shownCursor() set];
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
- (void)mouseMoved:(NSEvent *)event {
  // AppKit sets its own pointer at a window edge; back in the view, show Lean's again.
  // Over a resize zone the pump shows the zone's pointer (hoverEdgeCursor).
  if (!hoverEdges && NSCursor.currentCursor!=shownCursor()) [shownCursor() set];
  [self sendPointer:event type:3];
}
- (void)mouseDragged:(NSEvent *)event { [self sendPointer:event type:3]; }
- (void)mouseUp:(NSEvent *)event { [self sendPointer:event type:4]; }
// Kind 13, a right click (two-finger click on a trackpad): Lean may open the address menu (WebShell
// opensMenu, `how` context). An older host ignores the kind.
- (void)rightMouseDown:(NSEvent *)event { [self sendPointer:event type:13]; }
- (void)scrollWheel:(NSEvent *)event {
  // Backing pixels. Up is positive in Cocoa; the page moves the same way.
  CGFloat scale=self.window.backingScaleFactor;
  CGFloat step=event.hasPreciseScrollingDeltas ? event.scrollingDeltaY : event.scrollingDeltaY*16;
  enqueue(11,(int32_t)(step*scale),0);
  // Kind 12, a trackpad gesture across (back and forward swipes, WebGesture.lean): a is the
  // horizontal content movement in backing pixels (right is positive, as Cocoa has it); b is
  // the gesture phase (NSEventPhase: 1 began, 4 changed, 8 ended, 16 cancelled, 32 may
  // begin), its momentum phase times 256, and 65536 when System Settings has "Swipe between
  // pages" on. A mouse wheel has no phase and sends none. An older host ignores the kind.
  NSEventPhase phase=event.phase,momentum=event.momentumPhase;
  if (phase==NSEventPhaseNone && momentum==NSEventPhaseNone) return;
  int32_t flags=(int32_t)(phase&0xff)|(int32_t)((momentum&0xff)<<8)|(NSEvent.isSwipeTrackingFromScrollEventsEnabled?65536:0);
  enqueue(12,(int32_t)(event.scrollingDeltaX*scale),flags);
}
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
// Kind 14 cancels a press; focus loss must never activate a link.
- (void)windowDidResignKey:(NSNotification *)note { (void)note; enqueue(14,0,0); }
- (void)windowDidChangeOcclusionState:(NSNotification *)note { (void)note; enqueue(8,canPresent(),0); }
- (NSApplicationTerminateReply)applicationShouldTerminate:(NSApplication *)sender {
  (void)sender; enqueue(6,0,0); return NSTerminateCancel;
}
@end

// Bring the app to the front: on macOS 14 and later through cooperative activation.
static void activateApp(void) {
  if (@available(macOS 14.0, *)) [NSApp activate];
  else [NSApp activateIgnoringOtherApps:YES];
}
int ng_is_main_thread(void) { return pthread_main_np(); }
void ng_set_content_size(uint32_t width, uint32_t height) {
  if (!pthread_main_np() || !window) return;
  @autoreleasepool { [window setContentSize:NSMakeSize(width,height)]; }
}
void ng_set_input_trace(int enabled) { traceInput=enabled;rawMoveTraced=0;viewMoveTraced=0; }
int ng_can_present(void) { return canPresent(); }
void ng_show_after_surface(void) {
  if (!pthread_main_np() || offscreenScale>0) return;
  @autoreleasepool {
    // UnsafeWindowSurface can request pathless FFI permission from Terminal,
    // obscuring our window. Restore focus once after that constructor returns.
    [window makeKeyAndOrderFront:nil];
    activateApp();
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
    NSSize backing=backingSize(content);
    out[7]=backing.width; out[8]=backing.height;
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
    NSString *text=[pasteboard() stringForType:NSPasteboardTypeString] ?: @"";
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
    NSPasteboard *board=pasteboard();
    [board clearContents];
    return [board setString:value forType:NSPasteboardTypeString] ? 1 : 0;
  }
}
// Hand a URL to the user's default browser. Lean decides when.
int ng_open_url(const char *text) {
  @autoreleasepool {
    NSString *value=[NSString stringWithUTF8String:text];
    NSURL *url=value ? [NSURL URLWithString:value] : nil;
    if (!url || !([url.scheme isEqualToString:@"https"] || [url.scheme isEqualToString:@"http"])) return 0;
    return [[NSWorkspace sharedWorkspace] openURL:url] ? 1 : 0;
  }
}
// File > Open File… and Save Page As…: the system panels. Each answers a path owned by the
// caller until ng_free, or NULL when the person cancels. Only the host reads or writes it.
static char *copyPath(NSURL *url) {
  const char *path=url.fileSystemRepresentation;
  if (!path) return NULL;
  size_t length=strlen(path);
  char *copy=malloc(length+1);
  if (copy) memcpy(copy,path,length+1);
  return copy;
}
char *ng_open_file_panel(void) {
  if (!pthread_main_np()) return NULL;
  @autoreleasepool {
    NSOpenPanel *panel=[NSOpenPanel openPanel];
    panel.canChooseFiles=YES;panel.canChooseDirectories=NO;panel.allowsMultipleSelection=NO;
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-declarations"
    panel.allowedFileTypes=@[@"html",@"htm",@"svg",@"xhtml"];
#pragma clang diagnostic pop
    if ([panel runModal]!=NSModalResponseOK || !panel.URL) return NULL;
    return copyPath(panel.URL);
  }
}
char *ng_save_file_panel(const char *name) {
  if (!pthread_main_np()) return NULL;
  @autoreleasepool {
    NSSavePanel *panel=[NSSavePanel savePanel];
    NSString *value=name ? [NSString stringWithUTF8String:name] : nil;
    if (value.length) panel.nameFieldStringValue=value;
    if ([panel runModal]!=NSModalResponseOK || !panel.URL) return NULL;
    return copyPath(panel.URL);
  }
}
// The person's Reduce motion setting (Accessibility > Display): the splash only fades.
int ng_reduce_motion(void) {
  if (!pthread_main_np()) return 0;
  return NSWorkspace.sharedWorkspace.accessibilityDisplayShouldReduceMotion ? 1 : 0;
}
// Lean says which history moves exist. The menu only shows the answer.
static BOOL canGoBack=NO,canGoForward=NO;
void ng_set_history(int back,int forward) { canGoBack=back!=0;canGoForward=forward!=0; }
// Menu commands reach Lean as numbers. AppKit resolves the keyboard layout.
@interface NGMenuTarget : NSObject
@end
@implementation NGMenuTarget
- (void)command:(NSMenuItem *)item { enqueue(10,(int32_t)item.tag,0); }
- (BOOL)validateMenuItem:(NSMenuItem *)item {
  return item.tag==6 ? canGoBack : item.tag==7 ? canGoForward : YES;
}
@end
static NGMenuTarget *menuTarget;
static NSMenuItem *commandItem(NSMenu *menu,NSString *title,NSString *key,NSInteger command) {
  NSMenuItem *item=[menu addItemWithTitle:title action:@selector(command:) keyEquivalent:key];
  item.target=menuTarget;item.tag=command;
  return item;
}
// The same command under its shifted key: Command-+ and Command-_.
static void hiddenCommand(NSMenu *menu,NSString *title,NSString *key,NSInteger command) {
  NSMenuItem *item=commandItem(menu,title,key,command);
  item.hidden=YES;item.allowsKeyEquivalentWhenHidden=YES;
}
// A key with Control and no Command: Control-Tab and Control-Shift-Tab.
static void controlCommand(NSMenu *menu,NSString *title,NSString *key,NSEventModifierFlags flags,NSInteger command) {
  NSMenuItem *item=commandItem(menu,title,key,command);
  item.keyEquivalentModifierMask=flags;item.hidden=YES;item.allowsKeyEquivalentWhenHidden=YES;
}
// The standard menu. The command numbers and keys are those of Lean's key table
// (WebHistory.keyTable); the menu takes the keys with Command and Control-Tab. Quit reaches applicationShouldTerminate, which sends the host
// a close event, and Close goes through windowShouldClose. Page keys stay with Lean.
static void installMenu(void) {
  NSString *name=NSProcessInfo.processInfo.processName;
  NSMenu *bar=[[NSMenu alloc] init];
  NSMenuItem *appItem=[bar addItemWithTitle:name action:nil keyEquivalent:@""];
  NSMenu *appMenu=[[NSMenu alloc] initWithTitle:name];
  // About Foafnaut (issue 416): opens about:foafnaut in a new tab.
  commandItem(appMenu,@"About Foafnaut",@"",41);
  [appMenu addItem:[NSMenuItem separatorItem]];
  [appMenu addItemWithTitle:[@"Hide " stringByAppendingString:name] action:@selector(hide:) keyEquivalent:@"h"];
  [appMenu addItem:[NSMenuItem separatorItem]];
  [appMenu addItemWithTitle:[@"Quit " stringByAppendingString:name] action:@selector(terminate:) keyEquivalent:@"q"];
  appItem.submenu=appMenu;
  menuTarget=[[NGMenuTarget alloc] init];
  NSMenuItem *fileItem=[bar addItemWithTitle:@"File" action:nil keyEquivalent:@""];
  NSMenu *fileMenu=[[NSMenu alloc] initWithTitle:@"File"];
  commandItem(fileMenu,@"New Tab",@"t",10);
  commandItem(fileMenu,@"Open File\u2026",@"o",44);
  commandItem(fileMenu,@"Open Location",@"l",9);
  [fileMenu addItem:[NSMenuItem separatorItem]];
  commandItem(fileMenu,@"Close Tab",@"w",11);
  [fileMenu addItemWithTitle:@"Close Window" action:@selector(performClose:) keyEquivalent:@"W"];
  commandItem(fileMenu,@"Reopen Closed Tab",@"T",20);
  commandItem(fileMenu,@"Settings",@",",12);
  [fileMenu addItem:[NSMenuItem separatorItem]];
  commandItem(fileMenu,@"Save Page As\u2026",@"s",45);
  [fileMenu addItem:[NSMenuItem separatorItem]];
  // Page Setup is the system panel; it changes the paper that Print lays out for.
  [fileMenu addItemWithTitle:@"Page Setup\u2026" action:@selector(runPageLayout:) keyEquivalent:@"P"];
  commandItem(fileMenu,@"Print\u2026",@"p",18);
  fileItem.submenu=fileMenu;
  NSMenuItem *editItem=[bar addItemWithTitle:@"Edit" action:nil keyEquivalent:@""];
  NSMenu *editMenu=[[NSMenu alloc] initWithTitle:@"Edit"];
  // Lean edits the address bar and the page selection; these only send the command.
  commandItem(editMenu,@"Undo",@"z",16);
  commandItem(editMenu,@"Redo",@"Z",17);
  [editMenu addItem:[NSMenuItem separatorItem]];
  commandItem(editMenu,@"Cut",@"x",15);
  commandItem(editMenu,@"Copy",@"c",4);
  commandItem(editMenu,@"Paste",@"v",14);
  commandItem(editMenu,@"Select All",@"a",5);
  [editMenu addItem:[NSMenuItem separatorItem]];
  commandItem(editMenu,@"Find\u2026",@"f",32);
  commandItem(editMenu,@"Find Next",@"g",42);
  commandItem(editMenu,@"Find Previous",@"G",43);
  editItem.submenu=editMenu;
  NSMenuItem *viewItem=[bar addItemWithTitle:@"View" action:nil keyEquivalent:@""];
  NSMenu *viewMenu=[[NSMenu alloc] initWithTitle:@"View"];
  commandItem(viewMenu,@"Reload Page",@"r",8);
  hiddenCommand(viewMenu,@"Reload Page",@"R",8);
  commandItem(viewMenu,@"Stop",@".",39);
  [viewMenu addItem:[NSMenuItem separatorItem]];
  commandItem(viewMenu,@"View Source",@"u",13);
  // The console tab (foafnaut:console): Option-Command-J, as in Safari and Chrome.
  commandItem(viewMenu,@"Console",@"j",40).keyEquivalentModifierMask=NSEventModifierFlagCommand|NSEventModifierFlagOption;
  commandItem(viewMenu,@"Actual Size",@"0",3);
  commandItem(viewMenu,@"Zoom In",@"=",1);
  hiddenCommand(viewMenu,@"Zoom In",@"+",1);
  commandItem(viewMenu,@"Zoom Out",@"-",2);
  hiddenCommand(viewMenu,@"Zoom Out",@"_",2);
  viewItem.submenu=viewMenu;
  NSMenuItem *historyItem=[bar addItemWithTitle:@"History" action:nil keyEquivalent:@""];
  NSMenu *historyMenu=[[NSMenu alloc] initWithTitle:@"History"];
  commandItem(historyMenu,@"Back",@"[",6);
  hiddenCommand(historyMenu,@"Back",[NSString stringWithFormat:@"%C",(unichar)NSLeftArrowFunctionKey],6);
  commandItem(historyMenu,@"Forward",@"]",7);
  hiddenCommand(historyMenu,@"Forward",[NSString stringWithFormat:@"%C",(unichar)NSRightArrowFunctionKey],7);
  historyItem.submenu=historyMenu;
  NSMenuItem *windowItem=[bar addItemWithTitle:@"Window" action:nil keyEquivalent:@""];
  NSMenu *windowMenu=[[NSMenu alloc] initWithTitle:@"Window"];
  [windowMenu addItemWithTitle:@"Minimize" action:@selector(performMiniaturize:) keyEquivalent:@"m"];
  [windowMenu addItem:[NSMenuItem separatorItem]];
  commandItem(windowMenu,@"Show Previous Tab",@"{",31);
  commandItem(windowMenu,@"Show Next Tab",@"}",30);
  controlCommand(windowMenu,@"Show Next Tab",@"\t",NSEventModifierFlagControl,30);
  controlCommand(windowMenu,@"Show Previous Tab",@"\t",NSEventModifierFlagControl|NSEventModifierFlagShift,31);
  for (NSInteger tab=1;tab<=8;tab++)
    commandItem(windowMenu,[NSString stringWithFormat:@"Select Tab %ld",(long)tab],[NSString stringWithFormat:@"%ld",(long)tab],20+tab);
  commandItem(windowMenu,@"Select Last Tab",@"9",29);
  windowItem.submenu=windowMenu;
  NSApp.mainMenu=bar;
}
// Repeatable checks with no OS focus: real menu key matching, and input events.
int ng_test_key(const char *key,int shift) {
  if (!pthread_main_np() || !window || !key) return 0;
  NSString *text=[NSString stringWithUTF8String:key];
  // An arrow key event carries a function key character and these two flags.
  BOOL left=strcmp(key,"left")==0,right=strcmp(key,"right")==0;
  NSEventModifierFlags arrow=left||right?NSEventModifierFlagFunction|NSEventModifierFlagNumericPad:0;
  if (left||right) text=[NSString stringWithFormat:@"%C",(unichar)(left?NSLeftArrowFunctionKey:NSRightArrowFunctionKey)];
  NSEvent *event=[NSEvent keyEventWithType:NSEventTypeKeyDown location:NSZeroPoint
    modifierFlags:NSEventModifierFlagCommand|arrow|(shift?NSEventModifierFlagShift:0) timestamp:0
    windowNumber:window.windowNumber context:nil characters:text charactersIgnoringModifiers:text
    isARepeat:NO keyCode:left?123:right?124:0];
  return [NSApp.mainMenu performKeyEquivalent:event] ? 1 : 0;
}
// A sweep must present. Float above other windows, and take no focus from them.
void ng_test_raise(void) {
  if (!pthread_main_np() || !window || offscreenScale>0) return;
  window.level=NSFloatingWindowLevel;[window orderFrontRegardless];
}
void ng_test_event(uint32_t kind,int32_t a,int32_t b) { enqueue(kind,a,b); }
// The app as macOS sees it: a regular app, in the Dock and in Command-Tab, with its
// menu. The host calls this first, before it loads the engine, so the Dock icon
// stops bouncing at once; ng_create calls it too. It runs once.
static int appStarted;
void ng_app_start(void) {
  if (!pthread_main_np() || appStarted || offscreenScale>0) return;
  appStarted=1;
  @autoreleasepool {
    // A wrapper app runs a program outside its bundle, so macOS would show the file
    // name in the menu bar. The wrapper names the app; this must precede NSApp.
    const char *appName=getenv("FACTOIDAL_APP_NAME");
    if (appName && *appName) NSProcessInfo.processInfo.processName=[NSString stringWithUTF8String:appName];
    [NSApplication sharedApplication];
    [NSApp setActivationPolicy:NSApplicationActivationPolicyRegular];
    delegate = [[NGDelegate alloc] init];
    NSApp.delegate = delegate;
    installMenu();
    [NSApp finishLaunching];
    activateApp();
  }
}
// What macOS says about this app: [regular policy, active, frontmost window is ours].
void ng_app_state(int32_t *out) {
  out[0]=out[1]=out[2]=0;
  if (!pthread_main_np() || !appStarted) return;
  out[0]=NSApp.activationPolicy==NSApplicationActivationPolicyRegular;
  out[1]=NSApp.active;
  out[2]=window && window.keyWindow;
}
void *ng_create(uint32_t width, uint32_t height) {
  if (!pthread_main_np() || window) return NULL;
  ng_app_start();
  @autoreleasepool {
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
    activateApp();
    resizeEvent();
    [NSApp updateWindows];
    [CATransaction flush];
    return (__bridge void *)content;
  }
}
// The same window and view as ng_create, never ordered on screen: no Dock icon, no
// activation, no focus taken. Events reach the same queue (ng_test_event, and the
// resize events of ng_set_content_size); the host draws into a GPU texture.
void *ng_create_offscreen(uint32_t width, uint32_t height, double scale) {
  if (!pthread_main_np() || window || appStarted || !(scale>0)) return NULL;
  offscreenScale=scale;
  @autoreleasepool {
    [NSApplication sharedApplication];
    [NSApp setActivationPolicy:NSApplicationActivationPolicyProhibited];
    delegate = [[NGDelegate alloc] init];
    NSApp.delegate = delegate;
    installMenu();
    [NSApp finishLaunching];
    window = [[NSWindow alloc] initWithContentRect:NSMakeRect(0,0,width,height)
      styleMask:NSWindowStyleMaskTitled|NSWindowStyleMaskClosable|NSWindowStyleMaskMiniaturizable|NSWindowStyleMaskResizable
      backing:NSBackingStoreBuffered defer:NO];
    window.releasedWhenClosed = NO;
    window.contentMinSize = NSMakeSize(192,128);
    window.contentMaxSize = NSMakeSize(2048,2048);
    window.delegate = delegate;
    content = [[NGView alloc] initWithFrame:NSMakeRect(0,0,width,height)];
    content.wantsLayer = YES;
    window.contentView = content;
    [window makeFirstResponder:content];
    resizeEvent();
    return (__bridge void *)content;
  }
}
int ng_offscreen(void) { return offscreenScale>0; }
// Window edge drag, done here so JS keeps running. In [NSApp sendEvent:] AppKit
// tracks a resize in its own loop until the mouse is up, and this host only runs
// JS between pumps, so Lean could not lay out the page during the drag.
// The zones are AppKit's (issue 424): a band 5 points either side of each edge, and
// 12 points along each edge from a corner, where both directions resize. The top
// band is the top of the title bar, as in other Mac windows; the title bar's buttons
// keep their clicks and the rest of it still drags the window.
enum { EdgeLeft=1, EdgeRight=2, EdgeBottom=4, EdgeTop=8 };
static const CGFloat edgeBand=5, cornerSpan=12;
static NSPoint resizeMouse;
static NSRect resizeFrame;
static NSPoint screenPoint(NSEvent *event) {
  return event.window ? [event.window convertPointToScreen:event.locationInWindow] : event.locationInWindow;
}
static int resizeEdgesAt(NSPoint p) {
  if (!window || !(window.styleMask&NSWindowStyleMaskResizable) || (window.styleMask&NSWindowStyleMaskFullScreen) ||
      window.miniaturized) return 0;
  NSRect f=window.frame, inner=NSInsetRect(f,edgeBand,edgeBand);
  if (!NSPointInRect(p,NSInsetRect(f,-edgeBand,-edgeBand)) || NSPointInRect(p,inner)) return 0;
  for (NSWindowButton kind=NSWindowCloseButton; kind<=NSWindowZoomButton; kind++) {
    NSButton *button=[window standardWindowButton:kind];
    if (!button || button.hiddenOrHasHiddenAncestor) continue;
    NSRect r=[window convertRectToScreen:[button convertRect:button.bounds toView:nil]];
    if (NSPointInRect(p,r)) return 0;
  }
  int edges=(p.x<NSMinX(inner)?EdgeLeft:p.x>=NSMaxX(inner)?EdgeRight:0)|
    (p.y<NSMinY(inner)?EdgeBottom:p.y>=NSMaxY(inner)?EdgeTop:0);
  if (!(edges&(EdgeTop|EdgeBottom)))
    edges|=p.y<NSMinY(f)+cornerSpan?EdgeBottom:p.y>=NSMaxY(f)-cornerSpan?EdgeTop:0;
  if (!(edges&(EdgeLeft|EdgeRight)))
    edges|=p.x<NSMinX(f)+cornerSpan?EdgeLeft:p.x>=NSMaxX(f)-cornerSpan?EdgeRight:0;
  return edges;
}
// The pointer for a zone: the system's frame resize pointers on macOS 15, else the
// public two-way pointers (macOS before 15 has no public diagonal one).
static NSCursor *resizeCursor(int edges) {
  int h=edges&(EdgeLeft|EdgeRight), v=edges&(EdgeTop|EdgeBottom);
  if (@available(macOS 15.0, *)) {
    NSCursorFrameResizePosition position=
      h==EdgeLeft&&v==EdgeTop ? NSCursorFrameResizePositionTopLeft :
      h==EdgeRight&&v==EdgeTop ? NSCursorFrameResizePositionTopRight :
      h==EdgeLeft&&v==EdgeBottom ? NSCursorFrameResizePositionBottomLeft :
      h==EdgeRight&&v==EdgeBottom ? NSCursorFrameResizePositionBottomRight :
      h==EdgeLeft ? NSCursorFrameResizePositionLeft : h==EdgeRight ? NSCursorFrameResizePositionRight :
      v==EdgeTop ? NSCursorFrameResizePositionTop : NSCursorFrameResizePositionBottom;
    return [NSCursor frameResizeCursorFromPosition:position inDirections:NSCursorFrameResizeDirectionsAll];
  }
  return v&&!h ? NSCursor.resizeUpDownCursor : h&&!v ? NSCursor.resizeLeftRightCursor : NSCursor.crosshairCursor;
}
static int beginEdgeResize(NSEvent *event) {
  if (event.type!=NSEventTypeLeftMouseDown) return 0;
  NSPoint p=screenPoint(event);
  NSRect f=window.frame;
  if (traceInput) fprintf(stderr,"native mouse down at %.1f,%.1f; window %.1f,%.1f %.1fx%.1f; event window %s\n",
    p.x,p.y,f.origin.x,f.origin.y,f.size.width,f.size.height,event.window==window?"ours":"other");
  if (event.window!=window) return 0;
  int edges=resizeEdgesAt(p);
  if (!edges) return 0;
  resizeEdges=edges; resizeMouse=p; resizeFrame=f;
  [resizeCursor(edges) set];
  if (traceInput) fprintf(stderr,"native edge resize begins, edges %d\n",edges);
  return 1;
}
static int continueEdgeResize(NSEvent *event) {
  if (!resizeEdges) return 0;
  if (event.type==NSEventTypeLeftMouseUp) { resizeEdges=0; return 1; }
  if (event.type!=NSEventTypeLeftMouseDragged) return 0;
  NSPoint p=screenPoint(event);
  CGFloat dx=p.x-resizeMouse.x, dy=p.y-resizeMouse.y;
  NSRect f=resizeFrame;
  NSSize least=[window frameRectForContentRect:NSMakeRect(0,0,window.contentMinSize.width,window.contentMinSize.height)].size;
  NSSize most=[window frameRectForContentRect:NSMakeRect(0,0,window.contentMaxSize.width,window.contentMaxSize.height)].size;
  CGFloat mostTop=window.screen ? NSMaxY(window.screen.visibleFrame) : CGFLOAT_MAX;
  if (resizeEdges&EdgeRight) f.size.width=MIN(MAX(resizeFrame.size.width+dx,least.width),most.width);
  if (resizeEdges&EdgeLeft) {
    f.size.width=MIN(MAX(resizeFrame.size.width-dx,least.width),most.width);
    f.origin.x=NSMaxX(resizeFrame)-f.size.width;
  }
  if (resizeEdges&EdgeBottom) {
    f.size.height=MIN(MAX(resizeFrame.size.height-dy,least.height),most.height);
    f.origin.y=NSMaxY(resizeFrame)-f.size.height;
  }
  if (resizeEdges&EdgeTop) {
    // The bottom stays; the title bar does not go under the menu bar.
    CGFloat room=MAX(mostTop-NSMinY(resizeFrame),resizeFrame.size.height);
    f.size.height=MIN(MIN(MAX(resizeFrame.size.height+dy,least.height),most.height),room);
  }
  [resizeCursor(resizeEdges) set];
  if (!NSEqualRects(f,window.frame)) [window setFrame:f display:NO];
  return 1;
}
// Over a zone, show its pointer; leaving it, show Lean's again. The view leaves the
// pointer alone while hoverEdges is set.
static void hoverEdgeCursor(NSEvent *event) {
  if (event.type!=NSEventTypeMouseMoved || resizeEdges) return;
  int edges=event.window==window||!event.window ? resizeEdgesAt(screenPoint(event)) : 0;
  if (edges) [resizeCursor(edges) set];
  else if (hoverEdges) [shownCursor() set];
  hoverEdges=edges;
}
// Tests: post a left-button mouse event at a screen point (kind 2 down, 3 dragged,
// 4 up, 5 moved) for the next pump, and read the window frame and resize state:
// x, y, width, height in screen points, the hovered edges and the dragged edges.
void ng_test_mouse(uint32_t kind,double x,double y) {
  if (!pthread_main_np() || !window || kind<2 || kind>5) return;
  @autoreleasepool {
    NSEventType type=kind==2?NSEventTypeLeftMouseDown:kind==3?NSEventTypeLeftMouseDragged:
      kind==4?NSEventTypeLeftMouseUp:NSEventTypeMouseMoved;
    NSPoint local=[window convertPointFromScreen:NSMakePoint(x,y)];
    NSEvent *event=[NSEvent mouseEventWithType:type location:local modifierFlags:0 timestamp:NSProcessInfo.processInfo.systemUptime
      windowNumber:window.windowNumber context:nil eventNumber:0 clickCount:kind==5?0:1 pressure:kind==2||kind==3?1:0];
    [NSApp postEvent:event atStart:NO];
  }
}
void ng_test_window_frame(double *out) {
  out[0]=out[1]=out[2]=out[3]=out[4]=out[5]=0;
  if (!pthread_main_np() || !window) return;
  NSRect f=window.frame;
  out[0]=f.origin.x;out[1]=f.origin.y;out[2]=f.size.width;out[3]=f.size.height;
  out[4]=hoverEdges;out[5]=resizeEdges;
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
      hoverEdgeCursor(event);
    }
    [NSApp updateWindows];
    [CATransaction flush];
  }
}
int ng_next_event(void *out) {
  if (!pthread_main_np() || !eventCount) return 0;
  memcpy(out, events + eventHead, sizeof(struct NGEvent));
  eventCount--; eventHead = eventCount ? eventHead + 1 : 0;
  return 1;
}
void ng_hide(void) {
  if (!pthread_main_np()) return;
  @autoreleasepool { [window orderOut:nil]; }
  // Retain window/view and loaded dylib until process exit: the WebGPU surface
  // holds their native handles. Never free NSView underneath that surface.
}

// Printing (issue 1268). Lean lays the document out for the paper and draws each
// page; this hands the page images to the system print operation, which gives the
// print panel, Save as PDF and the printer. No layout or page decision is made here.
@interface NGPrintView : NSView
@property(nonatomic) NSArray<NSBitmapImageRep *> *pages;
@property(nonatomic) NSSize pageSize;
@end
@implementation NGPrintView
- (BOOL)isFlipped { return YES; }
- (BOOL)knowsPageRange:(NSRangePointer)range { *range=NSMakeRange(1,self.pages.count); return YES; }
- (NSRect)rectForPage:(NSInteger)page {
  return NSMakeRect(0,(page-1)*self.pageSize.height,self.pageSize.width,self.pageSize.height);
}
- (void)drawRect:(NSRect)dirty {
  for (NSUInteger i=0;i<self.pages.count;i++) {
    NSRect rect=NSMakeRect(0,i*self.pageSize.height,self.pageSize.width,self.pageSize.height);
    if (NSIntersectsRect(rect,dirty))
      [self.pages[i] drawInRect:rect fromRect:NSZeroRect operation:NSCompositingOperationCopy fraction:1 respectFlipped:YES hints:nil];
  }
}
@end
// The paper of the current page setup, in points: width, height, and the left,
// right, top and bottom margins.
void ng_print_paper(double *out) {
  @autoreleasepool {
    NSPrintInfo *info=NSPrintInfo.sharedPrintInfo;
    out[0]=info.paperSize.width;out[1]=info.paperSize.height;
    out[2]=info.leftMargin;out[3]=info.rightMargin;out[4]=info.topMargin;out[5]=info.bottomMargin;
  }
}
// Print `count` pages of RGBA pixels, each `width` by `height`, drawn at `pointWidth`
// by `pointHeight` points inside the margins of the shared page setup. With a PDF
// path the job is saved there with no panel (for tests); else the print panel shows,
// modal, as in other Mac apps. Returns the pages sent, 0 when cancelled, -1 on error.
int32_t ng_print(const uint8_t *rgba,uint32_t count,uint32_t width,uint32_t height,
    double pointWidth,double pointHeight,const char *title,const char *pdfPath) {
  if (!pthread_main_np() || !rgba || !count || !width || !height) return -1;
  @autoreleasepool {
    NSMutableArray<NSBitmapImageRep *> *pages=[NSMutableArray arrayWithCapacity:count];
    size_t bytes=(size_t)width*height*4;
    for (uint32_t i=0;i<count;i++) {
      NSBitmapImageRep *rep=[[NSBitmapImageRep alloc] initWithBitmapDataPlanes:NULL pixelsWide:width pixelsHigh:height
        bitsPerSample:8 samplesPerPixel:4 hasAlpha:YES isPlanar:NO colorSpaceName:NSDeviceRGBColorSpace
        bitmapFormat:NSBitmapFormatAlphaNonpremultiplied bytesPerRow:width*4 bitsPerPixel:32];
      if (!rep) return -1;
      memcpy(rep.bitmapData,rgba+i*bytes,bytes);
      rep.size=NSMakeSize(pointWidth,pointHeight);
      [pages addObject:rep];
    }
    NGPrintView *view=[[NGPrintView alloc] initWithFrame:NSMakeRect(0,0,pointWidth,pointHeight*count)];
    view.pages=pages;view.pageSize=NSMakeSize(pointWidth,pointHeight);
    NSPrintInfo *info=[NSPrintInfo.sharedPrintInfo copy];
    info.horizontalPagination=NSPrintingPaginationModeClip;
    info.verticalPagination=NSPrintingPaginationModeClip;
    info.horizontallyCentered=NO;info.verticallyCentered=NO;
    NSString *path=pdfPath&&*pdfPath?[NSString stringWithUTF8String:pdfPath]:nil;
    if (path) {
      info.jobDisposition=NSPrintSaveJob;
      info.dictionary[NSPrintJobSavingURL]=[NSURL fileURLWithPath:path];
    }
    NSPrintOperation *operation=[NSPrintOperation printOperationWithView:view printInfo:info];
    operation.jobTitle=title?[NSString stringWithUTF8String:title]:@"foafnaut";
    operation.showsPrintPanel=path==nil;
    operation.showsProgressPanel=path==nil;
    BOOL done=[operation runOperation];
    if (window && offscreenScale<=0) [window makeKeyAndOrderFront:nil];
    return done?(int32_t)count:0;
  }
}
