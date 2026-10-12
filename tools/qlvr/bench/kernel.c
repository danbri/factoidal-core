/* tools/qlvr/bench/kernel.c — the C reference for the q07 kernel
 * (https://github.com/danbri/factoidal/issues/778; record:
 * docs/designissues/2026-10-11-qlvr-performance.md).
 *
 * Reads the file `l4qlvr kernel-dump` writes and runs the same algorithm as
 * Harness/QlvrKernel.lean: filter A on (col0, col1) = (kA0, kA1) keeping
 * col2; filter B on col0 = kB0 keeping col1 and col2; merge join on ?i.
 * Prints the output rows, the checksum and the median and minimum time of
 * one run. NOT linked into the Lean library; a measurement tool only.
 *
 * `c-O2-copies` is `c-O2` plus the five buffer copies that the Lean kernels
 * make before they write (Harness/QlvrKernel.lean, `scratch`: each output
 * buffer starts as a copy of an input column). It measures what those
 * copies cost (docs/designissues/2026-10-12-lean-to-c-performance.md,
 * section 7).
 *
 * With glibc, main sets M_MMAP_THRESHOLD and M_TRIM_THRESHOLD to 1 GiB. With
 * the defaults, each 2 MB buffer of a run is an mmap that free returns to the
 * kernel, so every run pays about 1,100 page faults and the C kernel measured
 * 3 times slower than its loops (section 7). The Lean runtime (mimalloc)
 * keeps freed memory, so without this the comparison is not of the same work.
 *
 *   cc -O2 -o /tmp/qlvr-kernel tools/qlvr/bench/kernel.c
 *   /tmp/qlvr-kernel KERNEL-FILE [ITERS]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef __GLIBC__
#include <malloc.h>
#endif

static uint64_t now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y;
}

static const uint64_t MIX = 0x9E3779B97F4A7C15ull;

typedef struct { size_t rows; uint64_t sum; } result;

static result run(const uint64_t *a0, const uint64_t *a1, const uint64_t *a2, size_t nA,
                  const uint64_t *b0, const uint64_t *b1, const uint64_t *b2, size_t nB,
                  uint64_t kA0, uint64_t kA1, uint64_t kB0, int copies) {
  uint64_t *ai = malloc(8 * (nA + 1)), *bi = malloc(8 * (nB + 1)), *ba = malloc(8 * (nB + 1));
  size_t na = 0, nb = 0;
  if (copies) { memcpy(ai, a2, 8 * nA); memcpy(bi, b1, 8 * nB); memcpy(ba, b2, 8 * nB); }
  for (size_t i = 0; i < nA; i++)
    if (a0[i] == kA0 && a1[i] == kA1) ai[na++] = a2[i];
  for (size_t j = 0; j < nB; j++)
    if (b0[j] == kB0) { bi[nb] = b1[j]; ba[nb] = b2[j]; nb++; }
  uint64_t *oi = malloc(8 * (nb + 1)), *oa = malloc(8 * (nb + 1));
  if (copies) { memcpy(oi, b1, 8 * (nb < nB ? nb : nB)); memcpy(oa, b2, 8 * (nb < nB ? nb : nB)); }
  size_t cap = nb + 1, n = 0;
  size_t i = 0, j = 0;
  while (i < na && j < nb) {
    uint64_t x = ai[i], y = bi[j];
    if (x < y) i++;
    else if (y < x) j++;
    else {
      size_t ie = i + 1, je = j + 1;
      while (ie < na && ai[ie] == x) ie++;
      while (je < nb && bi[je] == x) je++;
      for (size_t p = i; p < ie; p++)
        for (size_t q = j; q < je; q++) {
          if (n == cap) { cap *= 2; oi = realloc(oi, 8 * cap); oa = realloc(oa, 8 * cap); }
          oi[n] = x; oa[n] = ba[q]; n++;
        }
      i = ie; j = je;
    }
  }
  uint64_t s = 0;
  for (size_t k = 0; k < n; k++) s += oi[k] * MIX + oa[k];
  free(ai); free(bi); free(ba); free(oi); free(oa);
  result r = { n, s };
  return r;
}

/* The production design of Bgp.scanFoldM since 2026-10-11: the rows with a
 * key prefix are one range of the sorted input (two binary searches), then
 * the same merge join. */
static size_t lower(const uint64_t *c0, const uint64_t *c1, size_t n, uint64_t k0, uint64_t k1,
                    int two, int strict) {
  size_t lo = 0, hi = n;
  while (lo < hi) {
    size_t mid = lo + (hi - lo) / 2;
    int cmp = c0[mid] < k0 ? -1 : c0[mid] > k0 ? 1 : 0;
    if (cmp == 0 && two) cmp = c1[mid] < k1 ? -1 : c1[mid] > k1 ? 1 : 0;
    if (cmp < 0 || (strict && cmp == 0)) lo = mid + 1; else hi = mid;
  }
  return lo;
}

static result run_range(const uint64_t *a0, const uint64_t *a1, const uint64_t *a2, size_t nA,
                        const uint64_t *b0, const uint64_t *b1, const uint64_t *b2, size_t nB,
                        uint64_t kA0, uint64_t kA1, uint64_t kB0) {
  size_t la = lower(a0, a1, nA, kA0, kA1, 1, 0), ha = lower(a0, a1, nA, kA0, kA1, 1, 1);
  size_t lb = lower(b0, b1, nB, kB0, 0, 0, 0), hb = lower(b0, b1, nB, kB0, 0, 0, 1);
  /* filtered copies, as the Lean side extracts them */
  size_t na = ha - la, nb = hb - lb;
  uint64_t *ai = malloc(8 * (na + 1)), *bi = malloc(8 * (nb + 1)), *ba = malloc(8 * (nb + 1));
  memcpy(ai, a2 + la, 8 * na); memcpy(bi, b1 + lb, 8 * nb); memcpy(ba, b2 + lb, 8 * nb);
  uint64_t *oi = malloc(8 * (nb + 1)), *oa = malloc(8 * (nb + 1));
  size_t cap = nb + 1, n = 0, i = 0, j = 0;
  while (i < na && j < nb) {
    uint64_t x = ai[i], y = bi[j];
    if (x < y) i++;
    else if (y < x) j++;
    else {
      size_t ie = i + 1, je = j + 1;
      while (ie < na && ai[ie] == x) ie++;
      while (je < nb && bi[je] == x) je++;
      for (size_t p = i; p < ie; p++)
        for (size_t q = j; q < je; q++) {
          if (n == cap) { cap *= 2; oi = realloc(oi, 8 * cap); oa = realloc(oa, 8 * cap); }
          oi[n] = x; oa[n] = ba[q]; n++;
        }
      i = ie; j = je;
    }
  }
  uint64_t s = 0;
  for (size_t k = 0; k < n; k++) s += oi[k] * MIX + oa[k];
  free(ai); free(bi); free(ba); free(oi); free(oa);
  result r = { n, s };
  return r;
}

int main(int argc, char **argv) {
#ifdef __GLIBC__
  mallopt(M_MMAP_THRESHOLD, 1 << 30);
  mallopt(M_TRIM_THRESHOLD, 1 << 30);
#endif
  if (argc < 2) { fprintf(stderr, "usage: kernel FILE [ITERS]\n"); return 2; }
  int iters = argc > 2 ? atoi(argv[2]) : 50;
  if (iters < 1) iters = 1;
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror(argv[1]); return 2; }
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  uint8_t *d = malloc((size_t)sz);
  if (fread(d, 1, (size_t)sz, f) != (size_t)sz) { fprintf(stderr, "short read\n"); return 2; }
  fclose(f);
  if (sz < 48 || memcmp(d, "QLVRKRN1", 8) != 0) { fprintf(stderr, "bad magic\n"); return 2; }
  uint64_t h[5];
  memcpy(h, d + 8, 40);
  uint64_t kA0 = h[0], kA1 = h[1], nA = h[2], kB0 = h[3], nB = h[4];
  if ((uint64_t)sz != 48 + 24 * nA + 24 * nB) { fprintf(stderr, "size mismatch\n"); return 2; }
  /* aligned copies of the columns */
  uint64_t *cols = malloc((size_t)(24 * nA + 24 * nB));
  memcpy(cols, d + 48, (size_t)(24 * nA + 24 * nB));
  const uint64_t *a0 = cols, *a1 = a0 + nA, *a2 = a1 + nA;
  const uint64_t *b0 = a2 + nA, *b1 = b0 + nB, *b2 = b1 + nB;
  uint64_t *ts = malloc(sizeof(uint64_t) * (size_t)iters);
  result r = { 0, 0 };
  for (int copies = 0; copies < 2; copies++) {
    for (int k = 0; k < iters; k++) {
      uint64_t t0 = now_ns();
      r = run(a0, a1, a2, nA, b0, b1, b2, nB, kA0, kA1, kB0, copies);
      uint64_t t1 = now_ns();
      ts[k] = t1 - t0;
    }
    qsort(ts, (size_t)iters, sizeof(uint64_t), cmp_u64);
    printf("kernel %s: A %llu rows, B %llu rows; output %zu rows, checksum %llu; us median %llu min %llu (%d runs)\n",
           copies ? "c-O2-copies" : "c-O2",
           (unsigned long long)nA, (unsigned long long)nB, r.rows, (unsigned long long)r.sum,
           (unsigned long long)(ts[(iters - 1) / 2] / 1000), (unsigned long long)(ts[0] / 1000), iters);
  }
  for (int k = 0; k < iters; k++) {
    uint64_t t0 = now_ns();
    r = run_range(a0, a1, a2, nA, b0, b1, b2, nB, kA0, kA1, kB0);
    uint64_t t1 = now_ns();
    ts[k] = t1 - t0;
  }
  qsort(ts, (size_t)iters, sizeof(uint64_t), cmp_u64);
  printf("kernel c-O2-range: A %llu rows, B %llu rows; output %zu rows, checksum %llu; us median %llu min %llu (%d runs)\n",
         (unsigned long long)nA, (unsigned long long)nB, r.rows, (unsigned long long)r.sum,
         (unsigned long long)(ts[(iters - 1) / 2] / 1000), (unsigned long long)(ts[0] / 1000), iters);
  return 0;
}
