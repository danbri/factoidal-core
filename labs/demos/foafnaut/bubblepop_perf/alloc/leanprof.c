#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef struct lp_site { const char * fn; const char * kind; int tag, nobj, ssz; uint64_t n, bytes; struct lp_site * next; int reg; } lp_site;
static lp_site * lp_head = 0;
uint64_t lp_numclass[2][8];
static void lp_dump(void) {
  const char * p = getenv("LEANPROF_OUT"); if (!p) return;
  FILE * f = fopen(p, "w"); if (!f) return;
  for (lp_site * s = lp_head; s; s = s->next) fprintf(f, "%s\t%s\t%d\t%d\t%d\t%llu\t%llu\n", s->fn, s->kind, s->tag, s->nobj, s->ssz, (unsigned long long)s->n, (unsigned long long)s->bytes);
  { static const char * nm[8] = {"+0", "int 1..255", "int29", "int32", "integer > int32", "-0", "NaN or infinity", "fraction"};
    for (int w = 0; w < 2; w++) for (int i = 0; i < 8; i++) fprintf(f, "%s\tnumclass:%s\t-1\t-1\t-1\t%llu\t0\n", w ? "float-register-write" : "boxed-number", nm[i], (unsigned long long)lp_numclass[w][i]); }
  fclose(f);
}
static int lp_installed = 0;
void lp_register(lp_site * s) { if (!lp_installed) { lp_installed = 1; atexit(lp_dump); } s->reg = 1; s->next = lp_head; lp_head = s; }
