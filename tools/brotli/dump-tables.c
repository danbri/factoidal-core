/* Writes the RFC 7932 transform list (Appendix B) and the context lookup table (section 7.1)
   of a google/brotli source tree as text, for tools/brotli/gen-brotli-data.py.
   Build: cc -I <brotli>/c/include -I <brotli>/c/common -o dump-tables dump-tables.c
   (compiled against <brotli>/c/common/transform.c and context.c by the generator). */
#include <stdio.h>
#include "transform.c"
#include "context.c"

int main(void) {
  const BrotliTransforms* t = BrotliGetTransforms();
  printf("transforms %d\n", (int)t->num_transforms);
  for (int i = 0; i < (int)t->num_transforms; i++) {
    const uint8_t* p = BROTLI_TRANSFORM_PREFIX(t, i);
    const uint8_t* s = BROTLI_TRANSFORM_SUFFIX(t, i);
    printf("%d|", BROTLI_TRANSFORM_TYPE(t, i));
    for (int k = 1; k <= p[0]; k++) printf("%02x", p[k]);
    printf("|");
    for (int k = 1; k <= s[0]; k++) printf("%02x", s[k]);
    printf("\n");
  }
  printf("context ");
  for (int i = 0; i < 2048; i++) printf("%02x", _kBrotliContextLookupTable[i]);
  printf("\n");
  return 0;
}
