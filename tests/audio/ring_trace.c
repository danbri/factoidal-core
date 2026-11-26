/* ring_trace.c — writes a trace of random single-threaded operations on the C ring of the audio
 * sink (capacity 7, 1 channel), for tests/audio/RingReplay.lean, which replays it through the
 * Lean model formal/lean4/L4Factoidal/WebAudio/Ring.lean.
 *
 *   w K TAKEN                 write of K frames answered TAKEN (K or 0)
 *   r K GAVE SILENT UNDERRUN  read of K frames gave GAVE frames, then SILENT frames of silence;
 *                             UNDERRUN is 1 when this read counted an under-run event
 *
 * Usage: ring_trace N SEED > trace.txt. Frame i holds the value i; the tool checks the frames it
 * reads are consecutive and exits 1 when they are not.
 */
#include <stdio.h>
#include <stdlib.h>

#include "audio_ring.h"

int main(int argc, char **argv) {
  long n = argc > 1 ? atol(argv[1]) : 100000;
  uint64_t rng = argc > 2 ? strtoull(argv[2], NULL, 10) : 1;
  if (rng == 0) rng = 1;
  l4_ring r;
  if (l4_ring_init(&r, 7, 1) != 0) return 2;
  uint64_t next_write = 0, next_read = 0;
  double wbuf[16];
  float rbuf[16];
  for (long op = 0; op < n; op++) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    uint32_t k = 1 + (uint32_t)((rng >> 20) % 9);          /* 1 to 9: sometimes more than the capacity */
    if ((rng >> 40) & 1) {
      for (uint32_t j = 0; j < k; j++) wbuf[j] = (double)(next_write + j);
      uint32_t taken = l4_ring_write_f64(&r, wbuf, k);
      next_write += taken;
      printf("w %u %u\n", k, taken);
    } else {
      uint64_t u0 = atomic_load(&r.underruns);
      uint32_t a = l4_ring_read(&r, rbuf, k);
      for (uint32_t j = 0; j < a; j++)
        if (rbuf[j] != (float)(next_read + j)) { fprintf(stderr, "ring_trace: wrong frame\n"); return 1; }
      for (uint32_t j = a; j < k; j++)
        if (rbuf[j] != 0.0f) { fprintf(stderr, "ring_trace: silence not zero\n"); return 1; }
      next_read += a;
      printf("r %u %u %u %u\n", k, a, k - a, (unsigned)(atomic_load(&r.underruns) - u0));
    }
  }
  l4_ring_destroy(&r);
  return 0;
}
