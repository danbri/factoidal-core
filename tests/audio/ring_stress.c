/* ring_stress.c — the C ring of the audio sink under two threads, and the sink's consumer thread,
 * for ThreadSanitizer (tests/audio/run.sh compiles this with -fsanitize=thread -O1 -g, together
 * with formal/lean4/ffi/audio_sink.c built with -DL4_AUDIO_NO_LEAN).
 *
 * Phase A: a writer thread writes TOTAL frames in random chunks of 1 to 600 frames (all or nothing;
 * a refused chunk is tried again); frame i holds the value f(i) = i mod 2^23 on both channels,
 * which a binary32 value holds exactly. A reader thread reads random sizes of 1 to 600 frames. The
 * reader checks every non-silent frame is f(next expected frame), every silent frame is zero, and
 * that its own count of under-run events and silent frames equals the ring's counters.
 *
 * Phase B: the same ring behind the sink's `null` consumer thread (the consumer drops the frames
 * at the sample rate): a writer writes 1 s of frames; the counters at the end must agree
 * (written == read, no frame lost).
 *
 * Exit code 0 and nothing printed by ThreadSanitizer when both phases pass.
 */
#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <sched.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "audio_ring.h"

#define TOTAL 20000000ull
#define CAP 4096u
#define CH 2u
#define MAXCHUNK 600u

static uint32_t rng_next(uint64_t *s) {
  uint64_t x = *s;
  x ^= x << 13; x ^= x >> 7; x ^= x << 17;
  *s = x;
  return (uint32_t)(x >> 16);
}

static double fval(uint64_t i) { return (double)(i & 0x7FFFFFu); }

static l4_ring ring;
static uint64_t expected_underruns, expected_silent, frames_read, bad_frames;

static void *writer_main(void *arg) {
  (void)arg;
  uint64_t rng = 0x9E3779B97F4A7C15ull;
  double *buf = (double *)malloc((size_t)MAXCHUNK * CH * sizeof(double));
  uint64_t next = 0;
  while (next < TOTAL) {
    uint32_t k = 1 + rng_next(&rng) % MAXCHUNK;
    if (k > TOTAL - next) k = (uint32_t)(TOTAL - next);
    for (uint32_t j = 0; j < k; j++)
      for (uint32_t c = 0; c < CH; c++) buf[(size_t)j * CH + c] = fval(next + j);
    while (l4_ring_write_f64(&ring, buf, k) == 0) sched_yield();   /* all or nothing; try again */
    next += k;
  }
  free(buf);
  return NULL;
}

static void *reader_main(void *arg) {
  (void)arg;
  uint64_t rng = 0xD1B54A32D192ED03ull;
  float *out = (float *)malloc((size_t)MAXCHUNK * CH * sizeof(float));
  uint64_t next = 0;
  while (next < TOTAL) {
    uint32_t k = 1 + rng_next(&rng) % MAXCHUNK;
    for (size_t i = 0; i < (size_t)k * CH; i++) out[i] = -1.0f;   /* the ring must overwrite every value */
    uint32_t a = l4_ring_read(&ring, out, k);
    if (a > k) { bad_frames++; break; }
    for (uint32_t j = 0; j < a; j++)
      for (uint32_t c = 0; c < CH; c++)
        if (out[(size_t)j * CH + c] != (float)fval(next + j)) bad_frames++;
    for (uint32_t j = a; j < k; j++)
      for (uint32_t c = 0; c < CH; c++)
        if (out[(size_t)j * CH + c] != 0.0f) bad_frames++;
    if (a < k) { expected_underruns++; expected_silent += k - a; }
    next += a;
    if (a == 0) sched_yield();
  }
  frames_read = next;
  free(out);
  return NULL;
}

int main(void) {
  int fails = 0;
  /* Phase A */
  if (l4_ring_init(&ring, CAP, CH) != 0) { fprintf(stderr, "ring: out of memory\n"); return 2; }
  pthread_t w, r;
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  pthread_create(&w, NULL, writer_main, NULL);
  pthread_create(&r, NULL, reader_main, NULL);
  pthread_join(w, NULL);
  pthread_join(r, NULL);
  clock_gettime(CLOCK_MONOTONIC, &t1);
  uint64_t ring_w = atomic_load(&ring.written), ring_r = atomic_load(&ring.read);
  uint64_t ring_u = atomic_load(&ring.underruns), ring_s = atomic_load(&ring.silent);
  printf("ring-stress A: %" PRIu64 " frames read in order, %" PRIu64 " bad values, written %" PRIu64
         ", read %" PRIu64 ", under-run events %" PRIu64 " (reader counted %" PRIu64
         "), silent frames %" PRIu64 " (reader counted %" PRIu64 "), %.1f s\n",
         frames_read, bad_frames, ring_w, ring_r, ring_u, expected_underruns, ring_s, expected_silent,
         (double)(t1.tv_sec - t0.tv_sec) + 1e-9 * (double)(t1.tv_nsec - t0.tv_nsec));
  if (bad_frames != 0) { printf("FAIL: wrong frame values\n"); fails++; }
  if (frames_read != TOTAL || ring_w != TOTAL || ring_r != TOTAL) { printf("FAIL: frame counts\n"); fails++; }
  if (ring_u != expected_underruns || ring_s != expected_silent) { printf("FAIL: under-run counters\n"); fails++; }
  l4_ring_destroy(&ring);

  /* Phase B */
  char err[200];
  l4_sink *s = l4_sink_open("null", 48000.0, 2, 4096, err, sizeof err);
  if (s == NULL) { printf("FAIL: open null: %s\n", err); return 1; }
  double buf[128 * 2];
  uint64_t frames = 0;
  for (int q = 0; q < 375; q++) {
    for (int j = 0; j < 128; j++) { buf[2 * j] = fval(frames + (uint64_t)j); buf[2 * j + 1] = buf[2 * j]; }
    uint32_t got;
    int spins = 0;
    while ((got = l4_sink_write_f64(s, buf, 256)) == 0 && spins++ < 5000) {
      struct timespec ts = {0, 1000000};
      nanosleep(&ts, NULL);
    }
    if (got != 128) { printf("FAIL: sink write took %u frames\n", got); fails++; break; }
    frames += 128;
  }
  double c[8];
  for (int spins = 0; spins < 5000; spins++) {
    l4_sink_counters(s, c);
    if (c[1] >= c[0]) break;
    struct timespec ts = {0, 1000000};
    nanosleep(&ts, NULL);
  }
  l4_sink_pause(s, 1);
  l4_sink_pause(s, 0);
  l4_sink_close(s);
  l4_sink_close(s);
  l4_sink_counters(s, c);
  printf("ring-stress B: null consumer: written %.0f, read %.0f, under-run events %.0f, silent frames %.0f\n",
         c[0], c[1], c[2], c[3]);
  if (c[0] != 48000.0 || c[1] != 48000.0) { printf("FAIL: sink counters\n"); fails++; }
  l4_sink_free(s);
  printf("ring-stress: %s\n", fails == 0 ? "pass" : "FAIL");
  return fails == 0 ? 0 : 1;
}
