/* audio_ring.h — the single-producer single-consumer ring of the audio sink, and the C API of
 * the sink behind the Lean externs.
 *
 * The ring follows formal/lean4/L4Factoidal/WebAudio/Ring.lean (design record:
 * docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13.5):
 *
 *   frame i is stored in slot i % capacity;
 *   write k: all or nothing: k frames are taken when k <= capacity - (written - read), else none;
 *   read k:  a = min(k, written - read) frames in order, then k - a frames of silence; when
 *            a < k one under-run event is counted and k - a is added to the silent frames.
 *
 * One thread writes (the rendering task), one thread reads (the consumer). Each side stores only
 * its own counter, with release order, after it has copied its frames; each side loads the other
 * side's counter with acquire order before it touches the slots that counter lets it touch.
 * The counters are frame counts and never wrap in practice (2^64 frames).
 *
 * The ring is `static inline` in this header so that tests/audio compile the same code that
 * audio_sink.c runs, under ThreadSanitizer, without a Lean runtime.
 */
#ifndef L4_AUDIO_RING_H
#define L4_AUDIO_RING_H

#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct l4_ring {
  uint32_t capacity;           /* frames */
  uint32_t channels;
  float *data;                 /* capacity * channels binary32 values, interleaved */
  _Atomic uint64_t written;    /* frames written; stored by the writer only */
  _Atomic uint64_t read;       /* frames read; stored by the reader only */
  _Atomic uint64_t underruns;  /* under-run events; stored by the reader only */
  _Atomic uint64_t silent;     /* frames of silence given; stored by the reader only */
} l4_ring;

/* 0 on success, -1 when memory is short. */
static inline int l4_ring_init(l4_ring *r, uint32_t capacity, uint32_t channels) {
  r->capacity = capacity;
  r->channels = channels;
  r->data = (float *)calloc((size_t)capacity * channels, sizeof(float));
  atomic_init(&r->written, 0);
  atomic_init(&r->read, 0);
  atomic_init(&r->underruns, 0);
  atomic_init(&r->silent, 0);
  return r->data == NULL ? -1 : 0;
}

static inline void l4_ring_destroy(l4_ring *r) {
  free(r->data);
  r->data = NULL;
}

/* Writer side. Takes `k` frames (`k * channels` binary64 values, converted to binary32) or none.
 * Answers k or 0. */
static inline uint32_t l4_ring_write_f64(l4_ring *r, const double *frames, uint32_t k) {
  uint64_t w = atomic_load_explicit(&r->written, memory_order_relaxed);
  uint64_t rd = atomic_load_explicit(&r->read, memory_order_acquire);
  uint64_t free_frames = (uint64_t)r->capacity - (w - rd);
  if (k == 0 || (uint64_t)k > free_frames) return 0;
  for (uint32_t j = 0; j < k; j++) {
    float *slot = r->data + (size_t)((w + j) % r->capacity) * r->channels;
    const double *src = frames + (size_t)j * r->channels;
    for (uint32_t c = 0; c < r->channels; c++) slot[c] = (float)src[c];
  }
  atomic_store_explicit(&r->written, w + k, memory_order_release);
  return k;
}

/* Reader side. Copies `min(k, written - read)` frames to `out` (k * channels values), fills the
 * rest of `out` with zeros, counts. Answers the number of frames taken. */
static inline uint32_t l4_ring_read(l4_ring *r, float *out, uint32_t k) {
  uint64_t w = atomic_load_explicit(&r->written, memory_order_acquire);
  uint64_t rd = atomic_load_explicit(&r->read, memory_order_relaxed);
  uint64_t avail = w - rd;
  uint32_t a = avail < k ? (uint32_t)avail : k;
  for (uint32_t j = 0; j < a; j++) {
    const float *slot = r->data + (size_t)((rd + j) % r->capacity) * r->channels;
    memcpy(out + (size_t)j * r->channels, slot, (size_t)r->channels * sizeof(float));
  }
  if (a < k) {
    memset(out + (size_t)a * r->channels, 0, (size_t)(k - a) * r->channels * sizeof(float));
    atomic_store_explicit(&r->underruns, atomic_load_explicit(&r->underruns, memory_order_relaxed) + 1,
                          memory_order_relaxed);
    atomic_store_explicit(&r->silent, atomic_load_explicit(&r->silent, memory_order_relaxed) + (k - a),
                          memory_order_relaxed);
  }
  atomic_store_explicit(&r->read, rd + a, memory_order_release);
  return a;
}

/* ---- The sink (audio_sink.c): a ring and one consumer thread. Plain C; the Lean externs are
 * thin wrappers (compiled out by L4_AUDIO_NO_LEAN, for the C tests). ---- */

typedef struct l4_sink l4_sink;

/* spec: "null", "wav:PATH" or "coreaudio". Answers NULL and writes the reason to err. */
l4_sink *l4_sink_open(const char *spec, double rate, uint32_t channels, uint32_t capacity,
                      char *err, size_t errlen);
/* Frames taken (n_values / channels), or 0 when the size is not a multiple of the channels. */
uint32_t l4_sink_write_f64(l4_sink *s, const double *interleaved, size_t n_values);
/* written, read, underrun events, silent frames, device latency frames, rate, channels, capacity. */
void l4_sink_counters(l4_sink *s, double out[8]);
void l4_sink_pause(l4_sink *s, int paused);
void l4_sink_close(l4_sink *s);   /* stops the consumer; safe to call twice */
void l4_sink_free(l4_sink *s);    /* closes, then frees; the sink is not used afterwards */
void l4_audio_device_info_c(const char *spec, double out[2]);

#endif
