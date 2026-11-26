/* audio_sink.c — the audio output of the web engine: a ring of binary32 frames and one consumer.
 *
 * Realises the `@[extern "l4_audio_*"]` opaques of formal/lean4/L4Factoidal/WebAudio/Sink.lean.
 * Design record: docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13 (issue
 * https://github.com/danbri/factoidal-core/issues/1169). The ring is audio_ring.h and follows
 * the state machine of formal/lean4/L4Factoidal/WebAudio/Ring.lean (theorems there: invariant,
 * frames read in order and once, silence and under-run count, no overwrite).
 *
 * The rule of this file: the C decides nothing about the audio. It copies frames, counts them and
 * keeps time. Every sample value comes from Lean (the rendering task); the C converts binary64 to
 * binary32 and nothing else.
 *
 * Consumers, chosen by a spec string:
 *   null       a thread of the sink takes 256 frames per period, at the sample rate, and drops
 *              them. The period deadlines are absolute (CLOCK_MONOTONIC), so the pace does not drift.
 *   wav:PATH   as `null`, and the taken frames, silence included, go to PATH as a WAVE_FORMAT_IEEE_FLOAT
 *              32-bit WAV file; the sizes in the header are patched when the sink closes. For tests.
 *   coreaudio  macOS: the default output unit. NOT written yet: see the marked place below. Until
 *              then it answers an error.
 * A paused consumer takes nothing and counts no under-run. Neither does a consumer before the
 * first write: it waits (sleeping) until frames written > 0 and starts its period clock then, so
 * the time between open and the first render quantum is not an under-run. (The CoreAudio consumer
 * does the same: it starts the output unit at the first write.) Ring.lean has no time and is
 * unchanged by this rule.
 *
 * The Wasm build has no audio output: every open fails ("no audio output in the Wasm build") and
 * no thread symbol is used.
 *
 * Named assumption of the macOS consumer, for every path that uses it: "CoreAudio plays the
 * frames it is given, in order, at the device rate".
 */
#if !defined(__APPLE__) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "audio_ring.h"

#ifndef L4_AUDIO_NO_LEAN
#include <lean/lean.h>
#endif

#ifndef __EMSCRIPTEN__
#include <pthread.h>
#include <time.h>
#endif

#define L4_PERIOD_FRAMES 256u

enum { SINK_NULL = 0, SINK_WAV = 1, SINK_COREAUDIO = 2 };

struct l4_sink {
  l4_ring ring;
  double rate;
  int kind;
  _Atomic int paused;
  _Atomic int stop;
  _Atomic int closed;
  int thread_started;
  FILE *wav;
  uint64_t wav_frames;
  float *scratch;                 /* L4_PERIOD_FRAMES * channels */
#ifndef __EMSCRIPTEN__
  pthread_t thread;
#endif
};

static void set_err(char *err, size_t errlen, const char *msg) {
  if (err != NULL && errlen > 0) snprintf(err, errlen, "%s", msg);
}

void l4_audio_device_info_c(const char *spec, double out[2]) {
  (void)spec;
  double rate = 48000.0;
  const char *env = getenv("FOAFNAUT_AUDIO_RATE");
  if (env != NULL && *env != '\0') {
    char *end = NULL;
    double v = strtod(env, &end);
    if (end != env && *end == '\0' && v >= 3000.0 && v <= 768000.0) rate = v;
  }
  out[0] = rate;
  out[1] = 2.0;
}

#ifdef __EMSCRIPTEN__

l4_sink *l4_sink_open(const char *spec, double rate, uint32_t channels, uint32_t capacity,
                      char *err, size_t errlen) {
  (void)spec; (void)rate; (void)channels; (void)capacity;
  set_err(err, errlen, "no audio output in the Wasm build");
  return NULL;
}
uint32_t l4_sink_write_f64(l4_sink *s, const double *interleaved, size_t n_values) {
  (void)s; (void)interleaved; (void)n_values;
  return 0;
}
void l4_sink_counters(l4_sink *s, double out[8]) {
  (void)s;
  memset(out, 0, 8 * sizeof(double));
}
void l4_sink_pause(l4_sink *s, int paused) { (void)s; (void)paused; }
void l4_sink_close(l4_sink *s) { (void)s; }
void l4_sink_free(l4_sink *s) { (void)s; }

#else /* POSIX */

static uint64_t now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

/* Sleeps for `ns` nanoseconds; an interrupted sleep returns early and the caller's loop checks the
 * clock again. (nanosleep, not clock_nanosleep: macOS has no clock_nanosleep.) */
static void sleep_ns(uint64_t ns) {
  struct timespec rel;
  rel.tv_sec = (time_t)(ns / 1000000000ull);
  rel.tv_nsec = (long)(ns % 1000000000ull);
  nanosleep(&rel, NULL);
}

/* ---- WAV file: RIFF, fmt (18 bytes, format 3, IEEE float), fact, data. 58 bytes of header. ---- */

static void put_u16(unsigned char *p, uint32_t v) { p[0] = (unsigned char)v; p[1] = (unsigned char)(v >> 8); }
static void put_u32(unsigned char *p, uint32_t v) {
  p[0] = (unsigned char)v; p[1] = (unsigned char)(v >> 8);
  p[2] = (unsigned char)(v >> 16); p[3] = (unsigned char)(v >> 24);
}

static void wav_header(unsigned char h[58], uint32_t rate, uint32_t channels, uint64_t frames) {
  uint64_t data = frames * channels * 4u;
  if (data > 0xFFFFFFFFull - 50u) data = (0xFFFFFFFFull - 50u) & ~3ull;
  memcpy(h, "RIFF", 4); put_u32(h + 4, (uint32_t)(50u + data));
  memcpy(h + 8, "WAVE", 4);
  memcpy(h + 12, "fmt ", 4); put_u32(h + 16, 18);
  put_u16(h + 20, 3);                          /* WAVE_FORMAT_IEEE_FLOAT */
  put_u16(h + 22, channels);
  put_u32(h + 24, rate);
  put_u32(h + 28, rate * channels * 4u);
  put_u16(h + 32, channels * 4u);
  put_u16(h + 34, 32);
  put_u16(h + 36, 0);                          /* cbSize */
  memcpy(h + 38, "fact", 4); put_u32(h + 42, 4); put_u32(h + 46, (uint32_t)frames);
  memcpy(h + 50, "data", 4); put_u32(h + 54, (uint32_t)data);
}

static int wav_write_frames(FILE *f, const float *v, size_t n_values) {
  unsigned char chunk[4096];
  size_t i = 0;
  while (i < n_values) {
    size_t m = n_values - i;
    if (m > sizeof(chunk) / 4) m = sizeof(chunk) / 4;
    for (size_t j = 0; j < m; j++) {
      uint32_t bits;
      memcpy(&bits, &v[i + j], 4);
      put_u32(chunk + 4 * j, bits);            /* little-endian whatever the host */
    }
    if (fwrite(chunk, 4, m, f) != m) return -1;
    i += m;
  }
  return 0;
}

/* ---- The consumer thread (kinds `null` and `wav`). ---- */

static void *consumer_main(void *arg) {
  l4_sink *s = (l4_sink *)arg;
  const double period_ns = (double)L4_PERIOD_FRAMES * 1e9 / s->rate;
  uint64_t periods = 0;
  int wav_ok = 1;
  /* Nothing is taken and no under-run is counted before the first write: wait (sleeping, as when
   * paused) until `written > 0`, and start the period clock then. */
  while (!atomic_load_explicit(&s->stop, memory_order_acquire) &&
         atomic_load_explicit(&s->ring.written, memory_order_acquire) == 0)
    sleep_ns(500000ull);
  uint64_t base = now_ns();
  while (!atomic_load_explicit(&s->stop, memory_order_acquire)) {
    if (atomic_load_explicit(&s->paused, memory_order_acquire)) {
      sleep_ns(1000000ull);
      base = now_ns();                         /* no catch-up burst after a pause */
      periods = 0;
      continue;
    }
    uint64_t due = base + (uint64_t)((double)periods * period_ns);
    uint64_t t = now_ns();
    if (t < due) { sleep_ns(due - t); continue; }
    if (t - due > 1000000000ull) { base = t; periods = 0; }   /* a stall over 1 s: restart the clock */
    l4_ring_read(&s->ring, s->scratch, L4_PERIOD_FRAMES);
    if (s->wav != NULL && wav_ok) {
      if (wav_write_frames(s->wav, s->scratch, (size_t)L4_PERIOD_FRAMES * s->ring.channels) != 0) wav_ok = 0;
      else s->wav_frames += L4_PERIOD_FRAMES;
    }
    periods++;
  }
  return NULL;
}

/* ---- Open, write, counters, pause, close. ---- */

/* The marked place for the `coreaudio` consumer (written by the coordinator, checked by the macOS
 * build of danbri/factoidal-builds; no CoreAudio code is here):
 *
 *   #if defined(__APPLE__) && !defined(L4_AUDIO_NO_DEVICE)
 *   ... open the default output AudioUnit; its render callback calls l4_ring_read(&s->ring, out,
 *       frames) and sets s->kind = SINK_COREAUDIO; report the device latency in the counters ...
 *   #endif
 */

l4_sink *l4_sink_open(const char *spec, double rate, uint32_t channels, uint32_t capacity,
                      char *err, size_t errlen) {
  int kind;
  const char *path = NULL;
  if (spec == NULL) { set_err(err, errlen, "bad audio sink spec (null pointer)"); return NULL; }
  if (strcmp(spec, "null") == 0) kind = SINK_NULL;
  else if (strncmp(spec, "wav:", 4) == 0 && spec[4] != '\0') { kind = SINK_WAV; path = spec + 4; }
  else if (strcmp(spec, "coreaudio") == 0) kind = SINK_COREAUDIO;
  else {
    char msg[300];
    snprintf(msg, sizeof msg, "bad audio sink spec '%.200s' (expected null, wav:PATH or coreaudio)", spec);
    set_err(err, errlen, msg);
    return NULL;
  }
  if (!(rate >= 3000.0 && rate <= 768000.0)) { set_err(err, errlen, "sample rate outside 3000 to 768000 Hz"); return NULL; }
  if (channels < 1 || channels > 32) { set_err(err, errlen, "channels outside 1 to 32"); return NULL; }
  if (capacity < 256 || capacity > 1048576) { set_err(err, errlen, "ring capacity outside 256 to 1048576 frames"); return NULL; }
  if (kind == SINK_COREAUDIO) { set_err(err, errlen, "no CoreAudio consumer in this build"); return NULL; }

  l4_sink *s = (l4_sink *)calloc(1, sizeof *s);
  if (s == NULL) { set_err(err, errlen, "out of memory"); return NULL; }
  s->rate = rate;
  s->kind = kind;
  atomic_init(&s->paused, 0);
  atomic_init(&s->stop, 0);
  atomic_init(&s->closed, 0);
  s->scratch = (float *)malloc((size_t)L4_PERIOD_FRAMES * channels * sizeof(float));
  if (l4_ring_init(&s->ring, capacity, channels) != 0 || s->scratch == NULL) {
    set_err(err, errlen, "out of memory");
    l4_ring_destroy(&s->ring); free(s->scratch); free(s);
    return NULL;
  }
  if (kind == SINK_WAV) {
    s->wav = fopen(path, "wb");
    unsigned char h[58];
    wav_header(h, (uint32_t)rate, channels, 0);
    if (s->wav == NULL || fwrite(h, 1, sizeof h, s->wav) != sizeof h) {
      char msg[300];
      snprintf(msg, sizeof msg, "file not writable: %.200s", path);
      set_err(err, errlen, msg);
      if (s->wav != NULL) fclose(s->wav);
      l4_ring_destroy(&s->ring); free(s->scratch); free(s);
      return NULL;
    }
  }
  if (pthread_create(&s->thread, NULL, consumer_main, s) != 0) {
    set_err(err, errlen, "audio consumer thread not started");
    if (s->wav != NULL) fclose(s->wav);
    l4_ring_destroy(&s->ring); free(s->scratch); free(s);
    return NULL;
  }
  s->thread_started = 1;
  return s;
}

uint32_t l4_sink_write_f64(l4_sink *s, const double *interleaved, size_t n_values) {
  if (atomic_load_explicit(&s->closed, memory_order_acquire)) return 0;
  uint32_t ch = s->ring.channels;
  if (n_values == 0 || n_values % ch != 0) return 0;
  size_t k = n_values / ch;
  if (k > s->ring.capacity) return 0;
  return l4_ring_write_f64(&s->ring, interleaved, (uint32_t)k);
}

void l4_sink_counters(l4_sink *s, double out[8]) {
  out[0] = (double)atomic_load_explicit(&s->ring.written, memory_order_acquire);
  out[1] = (double)atomic_load_explicit(&s->ring.read, memory_order_acquire);
  out[2] = (double)atomic_load_explicit(&s->ring.underruns, memory_order_relaxed);
  out[3] = (double)atomic_load_explicit(&s->ring.silent, memory_order_relaxed);
  out[4] = 0.0;                                /* device latency: none for `null` and `wav` */
  out[5] = s->rate;
  out[6] = (double)s->ring.channels;
  out[7] = (double)s->ring.capacity;
}

void l4_sink_pause(l4_sink *s, int paused) {
  atomic_store_explicit(&s->paused, paused != 0, memory_order_release);
}

void l4_sink_close(l4_sink *s) {
  if (atomic_exchange_explicit(&s->closed, 1, memory_order_acq_rel)) return;
  atomic_store_explicit(&s->stop, 1, memory_order_release);
  if (s->thread_started) { pthread_join(s->thread, NULL); s->thread_started = 0; }
  if (s->wav != NULL) {
    unsigned char h[58];
    wav_header(h, (uint32_t)s->rate, s->ring.channels, s->wav_frames);
    if (fseek(s->wav, 0, SEEK_SET) == 0) fwrite(h, 1, sizeof h, s->wav);
    fclose(s->wav);
    s->wav = NULL;
  }
}

void l4_sink_free(l4_sink *s) {
  if (s == NULL) return;
  l4_sink_close(s);
  l4_ring_destroy(&s->ring);
  free(s->scratch);
  free(s);
}

#endif /* __EMSCRIPTEN__ */

/* ---- The Lean externs. ---- */
#ifndef L4_AUDIO_NO_LEAN

static lean_external_class *g_sink_class = NULL;

static void sink_finalize(void *p) { l4_sink_free((l4_sink *)p); }
static void sink_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }

static void make_class(void) { g_sink_class = lean_register_external_class(sink_finalize, sink_foreach); }
#ifndef __EMSCRIPTEN__
static pthread_once_t g_class_once = PTHREAD_ONCE_INIT;
#endif

static lean_obj_res io_error(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res float_array(const double *v, size_t n) {
  lean_object *a = lean_alloc_sarray(sizeof(double), n, n);
  memcpy(lean_float_array_cptr(a), v, n * sizeof(double));
  return a;
}

/* The ABI of Lean 4.33: a function of type `IO a` takes no world argument and answers a
 * lean_io_result; a function of type `BaseIO a` takes no world argument and answers the value
 * itself (`UInt32` unboxed, `Unit` as lean_box(0)). The IR of Harness/AudioSinkTest.lean shows
 * the same for `lean_io_mono_ms_now`. */

LEAN_EXPORT lean_obj_res l4_audio_sink_open(b_lean_obj_arg spec, double rate, uint32_t channels,
                                            uint32_t capacity) {
  char err[320];
  err[0] = '\0';
  l4_sink *s = l4_sink_open(lean_string_cstr(spec), rate, channels, capacity, err, sizeof err);
  if (s == NULL) return io_error(err[0] != '\0' ? err : "audio sink not opened");
#ifndef __EMSCRIPTEN__
  pthread_once(&g_class_once, make_class);
#else
  if (g_sink_class == NULL) make_class();
#endif
  return lean_io_result_mk_ok(lean_alloc_external(g_sink_class, s));
}

static l4_sink *sink_of(b_lean_obj_arg o) { return (l4_sink *)lean_get_external_data(o); }

LEAN_EXPORT uint32_t l4_audio_sink_write(b_lean_obj_arg sink, b_lean_obj_arg frames) {
  return l4_sink_write_f64(sink_of(sink), lean_float_array_cptr(frames), lean_sarray_size(frames));
}

LEAN_EXPORT lean_obj_res l4_audio_sink_counters(b_lean_obj_arg sink) {
  double c[8];
  l4_sink_counters(sink_of(sink), c);
  return float_array(c, 8);
}

LEAN_EXPORT lean_obj_res l4_audio_sink_pause(b_lean_obj_arg sink, uint8_t paused) {
  l4_sink_pause(sink_of(sink), paused);
  return lean_box(0);
}

LEAN_EXPORT lean_obj_res l4_audio_sink_close(b_lean_obj_arg sink) {
  l4_sink_close(sink_of(sink));
  return lean_box(0);
}

LEAN_EXPORT lean_obj_res l4_audio_device_info(b_lean_obj_arg spec) {
  double v[2];
  l4_audio_device_info_c(lean_string_cstr(spec), v);
  return float_array(v, 2);
}

#endif /* L4_AUDIO_NO_LEAN */
