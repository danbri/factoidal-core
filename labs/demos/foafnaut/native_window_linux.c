/* Linux window and input transport. SDL owns the window, Deno presents the
   engine's WebGPU frames on its native surface. SDL never paints the page. */
#define _GNU_SOURCE
#include <SDL.h>
#include <SDL_syswm.h>
#include <SDL_vulkan.h>
#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <unistd.h>

/* `flags` (issue 1031), as in native_window.m: for pointer kinds 2, 4 and 13, bits 0-3 the
   modifiers (1 Shift, 2 Super, 4 Alt, 8 Control), bits 8-15 the click count, bits 16-17 the
   button (0 primary, 1 secondary, 2 middle). `ng_event_size` tells the host the size. */
typedef struct { uint32_t kind; int32_t a, b; uint32_t time; uint32_t flags; } NGEvent;
_Static_assert(sizeof(NGEvent) == 20, "window event ABI");
static SDL_Window *window;
static void *display_handle, *window_handle;
static int surface_system;  /* 1 X11, 2 Wayland */
static double offscreen_scale;
static int logical_width, logical_height, pixel_width, pixel_height;
static char *private_clipboard;
static int trace_input;
static SDL_Keymod text_modifiers;
static NGEvent *events;
static unsigned count, head, capacity, dropped;

int ng_is_main_thread(void) { return gettid() == getpid(); }
uint32_t ng_event_clock(void) { return SDL_GetTicks(); }
uint32_t ng_events_dropped(void) { return dropped; }

static void enqueue_flags(uint32_t kind, int32_t a, int32_t b, uint32_t flags) {
  if (count) {
    NGEvent *last = &events[head + count - 1];
    if ((kind == 1 || kind == 3) && last->kind == kind) {
      last->a = a; last->b = b; last->flags = flags; return;
    }
    if (kind == 11 && last->kind == 11) {
      int64_t sum = (int64_t)last->a + a;
      last->a = sum > INT32_MAX ? INT32_MAX : sum < INT32_MIN ? INT32_MIN : (int32_t)sum;
      return;
    }
  }
  if (head + count == capacity && head) {
    memmove(events, events + head, count * sizeof(*events)); head = 0;
  }
  if (count == capacity) {
    if (capacity == 65536) { ++dropped; return; }
    unsigned next = capacity ? 2 * capacity : 256;
    NGEvent *grown = realloc(events, next * sizeof(*events));
    if (!grown) { ++dropped; return; }
    events = grown; capacity = next;
  }
  events[head + count++] = (NGEvent){kind, a, b, ng_event_clock(), flags};
}
static void enqueue(uint32_t kind, int32_t a, int32_t b) { enqueue_flags(kind, a, b, 0); }
uint32_t ng_event_size(void) { return (uint32_t)sizeof(NGEvent); }
int ng_next_event(NGEvent *out) {
  if (!count || !out) return 0;
  *out = events[head++]; if (!--count) head = 0;
  return 1;
}
void ng_test_event(uint32_t kind, int32_t a, int32_t b) { enqueue(kind, a, b); }
void ng_test_event_flags(uint32_t kind, int32_t a, int32_t b, uint32_t flags) { enqueue_flags(kind, a, b, flags); }

static void resize_event(void) {
  if (window) {
    SDL_GetWindowSize(window, &logical_width, &logical_height);
    SDL_Vulkan_GetDrawableSize(window, &pixel_width, &pixel_height);
  } else {
    pixel_width = (int)lround(logical_width * offscreen_scale);
    pixel_height = (int)lround(logical_height * offscreen_scale);
  }
  enqueue(1, pixel_width, pixel_height);
}
static int valid_size(uint32_t w, uint32_t h) { return w > 0 && h > 0 && w <= 4096 && h <= 4096; }
void *ng_create(uint32_t w, uint32_t h) {
  if (window || offscreen_scale || !ng_is_main_thread() || !valid_size(w,h)) return NULL;
  if (SDL_InitSubSystem(SDL_INIT_VIDEO) < 0) goto fail;
  window = SDL_CreateWindow("Foafnaut", SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED, (int)w, (int)h,
                            SDL_WINDOW_VULKAN | SDL_WINDOW_ALLOW_HIGHDPI | SDL_WINDOW_RESIZABLE);
  if (!window) goto fail;
  SDL_SysWMinfo wm;
  SDL_VERSION(&wm.version);
  if (!SDL_GetWindowWMInfo(window, &wm)) goto fail;
  switch (wm.subsystem) {
#ifdef SDL_VIDEO_DRIVER_X11
    case SDL_SYSWM_X11:
      surface_system = 1; display_handle = wm.info.x11.display;
      window_handle = (void *)(uintptr_t)wm.info.x11.window; break;
#endif
#ifdef SDL_VIDEO_DRIVER_WAYLAND
    case SDL_SYSWM_WAYLAND:
      surface_system = 2; display_handle = wm.info.wl.display; window_handle = wm.info.wl.surface; break;
#endif
    default: SDL_SetError("unsupported window system %s", SDL_GetCurrentVideoDriver()); goto fail;
  }
  if (!display_handle || !window_handle) { SDL_SetError("missing native window or display"); goto fail; }
  SDL_SetWindowMinimumSize(window, 192, 128);
  SDL_StartTextInput();
  resize_event();
  return display_handle;
fail:
  fprintf(stderr, "Foafnaut could not create a Linux window: %s\n", SDL_GetError());
  if (window) SDL_DestroyWindow(window);
  window = NULL; display_handle = NULL; window_handle = NULL; surface_system = 0;
  SDL_QuitSubSystem(SDL_INIT_VIDEO);
  return NULL;
}
void *ng_create_offscreen(uint32_t w, uint32_t h, double scale) {
  if (window || offscreen_scale || !ng_is_main_thread() || !valid_size(w,h) ||
      !isfinite(scale) || scale <= 0 || scale > 8 || SDL_InitSubSystem(SDL_INIT_EVENTS) < 0) return NULL;
  offscreen_scale = scale; logical_width = (int)w; logical_height = (int)h;
  resize_event();
  return &offscreen_scale;
}
void *ng_window_handle(void) { return window_handle; }
int ng_surface_system(void) { return surface_system; }
int ng_can_present(void) {
  Uint32 flags = window ? SDL_GetWindowFlags(window) : 0;
  return (flags & SDL_WINDOW_SHOWN) && !(flags & (SDL_WINDOW_MINIMIZED | SDL_WINDOW_HIDDEN));
}
void ng_surface_state(double *out) {
  Uint32 flags = window ? SDL_GetWindowFlags(window) : 0;
  memset(out, 0, 18 * sizeof(*out));
  out[0] = ng_is_main_thread(); out[1] = !!(flags & SDL_WINDOW_SHOWN);
  out[2] = !!(flags & SDL_WINDOW_MINIMIZED); out[3] = window_handle != NULL;
  out[5] = logical_width; out[6] = logical_height; out[7] = pixel_width; out[8] = pixel_height;
  out[9] = logical_width ? (double)pixel_width / logical_width : 1;
  out[10] = logical_width; out[11] = logical_height; out[12] = pixel_width; out[13] = pixel_height;
  out[15] = ng_can_present(); out[17] = !!(flags & SDL_WINDOW_HIDDEN);
}
void ng_show_after_surface(void) { if (window) { SDL_ShowWindow(window); SDL_RaiseWindow(window); } }
void ng_hide(void) { if (window) SDL_HideWindow(window); }
void ng_set_title(const char *title) { if (window && title) SDL_SetWindowTitle(window, title); }
void ng_set_content_size(uint32_t w, uint32_t h) {
  if (!valid_size(w,h)) return;
  if (window) SDL_SetWindowSize(window, (int)w, (int)h);
  else if (offscreen_scale) { logical_width = (int)w; logical_height = (int)h; resize_event(); }
}
void ng_set_cursor(int kind) {
  static SDL_Cursor *cursors[3];
  static const SDL_SystemCursor shapes[] = {SDL_SYSTEM_CURSOR_ARROW, SDL_SYSTEM_CURSOR_HAND, SDL_SYSTEM_CURSOR_IBEAM};
  if (!window || kind < 0 || kind > 2) return;
  if (!cursors[kind]) cursors[kind] = SDL_CreateSystemCursor(shapes[kind]);
  if (cursors[kind]) SDL_SetCursor(cursors[kind]);
}
void ng_app_state(int32_t *out) {
  out[0] = window != NULL; out[1] = out[2] = window && SDL_GetKeyboardFocus() == window;
}
void ng_set_input_trace(int enabled) { trace_input = enabled; }

static int modifiers(SDL_Keymod mods) {
  return ((mods & KMOD_SHIFT) ? 1 : 0) | ((mods & KMOD_GUI) ? 2 : 0) |
         ((mods & KMOD_ALT) ? 4 : 0) | ((mods & KMOD_CTRL) ? 8 : 0);
}
static void pointer_flags(uint32_t kind, int x, int y, uint32_t flags) {
  if (logical_width && logical_height) {
    int px = (int)floor((double)x * pixel_width / logical_width);
    int py = (int)floor((double)y * pixel_height / logical_height);
    if (trace_input && kind != 3) fprintf(stderr, "Input SDL kind=%u backing=(%d,%d)\n", kind, px, py);
    enqueue_flags(kind, px, py, flags);
  }
}
static void pointer(uint32_t kind, int x, int y) { pointer_flags(kind, x, y, (uint32_t)modifiers(SDL_GetModState())); }
static void receive(const SDL_Event *event) {
  switch (event->type) {
    case SDL_QUIT: enqueue(6, 0, 0); break;
    case SDL_WINDOWEVENT:
      switch (event->window.event) {
        case SDL_WINDOWEVENT_SIZE_CHANGED: case SDL_WINDOWEVENT_DISPLAY_CHANGED: resize_event(); break;
        case SDL_WINDOWEVENT_CLOSE: enqueue(6, 0, 0); break;
        case SDL_WINDOWEVENT_FOCUS_LOST: enqueue(14, 0, 0); break;
        case SDL_WINDOWEVENT_SHOWN: case SDL_WINDOWEVENT_EXPOSED: case SDL_WINDOWEVENT_RESTORED:
        case SDL_WINDOWEVENT_HIDDEN: case SDL_WINDOWEVENT_MINIMIZED: enqueue(8, ng_can_present(), 0); break;
      }
      break;
    case SDL_MOUSEMOTION: pointer(3, event->motion.x, event->motion.y); break;
    case SDL_MOUSEBUTTONDOWN: case SDL_MOUSEBUTTONUP:
    {
      /* Modifiers, click count and button with each press (issue 1031). */
      uint32_t flags = (uint32_t)modifiers(SDL_GetModState()) | ((uint32_t)event->button.clicks << 8);
      uint32_t kind = event->type == SDL_MOUSEBUTTONDOWN ? 2 : 4;
      if (event->button.button == SDL_BUTTON_LEFT)
        pointer_flags(kind, event->button.x, event->button.y, flags);
      else if (event->button.button == SDL_BUTTON_MIDDLE)
        pointer_flags(kind, event->button.x, event->button.y, flags | (2u << 16));
      else if (event->type == SDL_MOUSEBUTTONDOWN && event->button.button == SDL_BUTTON_RIGHT)
        pointer_flags(13, event->button.x, event->button.y, flags | (1u << 16));
    }
      break;
    case SDL_MOUSEWHEEL: {
      double scale = logical_height ? (double)pixel_height / logical_height : 1;
      int direction = event->wheel.direction == SDL_MOUSEWHEEL_FLIPPED ? -1 : 1;
      enqueue(11, (int32_t)lround(event->wheel.preciseY * 16 * scale * direction), 0);
      break;
    }
    case SDL_KEYDOWN: case SDL_KEYUP:
      text_modifiers = (SDL_Keymod)event->key.keysym.mod;
      if (event->type == SDL_KEYDOWN &&
          !(event->key.keysym.sym >= SDLK_LCTRL && event->key.keysym.sym <= SDLK_RGUI))
        enqueue(16, event->key.keysym.sym, modifiers(text_modifiers));
      break;
    case SDL_TEXTINPUT: {
      if ((text_modifiers & (KMOD_CTRL | KMOD_GUI)) && !(text_modifiers & KMOD_MODE)) break;
      const char *text = event->text.text;
      uint32_t *chars = (uint32_t *)SDL_iconv_string("UTF-32LE", "UTF-8", text, strlen(text) + 1);
      if (chars) {
        for (const uint32_t *p = chars; *p; ++p) {
          uint32_t scalar = SDL_SwapLE32(*p);
          if (scalar >= 32 && scalar != 127) enqueue(9, (int32_t)scalar, 0);
        }
        SDL_free(chars);
      }
      break;
    }
  }
}
int ng_pump_quiet(void) {
  int pumped = 0;
  SDL_Event event;
  while (SDL_PollEvent(&event)) { receive(&event); ++pumped; }
  return pumped;
}
void ng_pump(void) { (void)ng_pump_quiet(); }
int ng_wait_event(double ms) {
  if (count) return 1;
  SDL_Event event;
  if (ms <= 0 || !isfinite(ms) || !SDL_WaitEventTimeout(&event, (int)fmin(ceil(ms), INT_MAX))) return 0;
  receive(&event); return 1;
}
void ng_test_raise(void) { if (window) SDL_RaiseWindow(window); }
int ng_test_key(const char *key, int shift) {
  if (!key || !*key) return 0;
  SDL_Keycode code = SDL_GetKeyFromName(key);
  if (code == SDLK_UNKNOWN) return 0;
  int mods = code == SDLK_LEFT || code == SDLK_RIGHT ? 4 : 8;
  enqueue(16, code, mods | (shift ? 1 : 0)); return 1;
}
/* An off-screen window has a private clipboard. SDL allocated the result of
   either path, and ng_free always uses the matching allocator. */
char *ng_clipboard_copy(void) {
  if (offscreen_scale) return SDL_strdup(private_clipboard ? private_clipboard : "");
  char *text = SDL_GetClipboardText();
  if (text && strlen(text) > 1024 * 1024) { SDL_free(text); return NULL; }
  return text;
}
void ng_free(void *p) { SDL_free(p); }
int ng_clipboard_write(const char *text) {
  if (!text || strlen(text) > 1024 * 1024) return 0;
  if (!offscreen_scale) return SDL_SetClipboardText(text) == 0;
  char *copy = SDL_strdup(text);
  if (!copy) return 0;
  SDL_free(private_clipboard); private_clipboard = copy; return 1;
}
int ng_open_url(const char *text) {
  return text && (!strncasecmp(text, "http://", 7) || !strncasecmp(text, "https://", 8)) && SDL_OpenURL(text) == 0;
}
