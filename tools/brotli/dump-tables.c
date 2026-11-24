/* Writes the RFC 7932 transform list (Appendix B) and the context lookup table (section 7.1)
   of a google/brotli source tree as text, for tools/brotli/gen-brotli-data.py.
   Build: cc -I <brotli>/c/include -I <brotli>/c/common -o dump-tables dump-tables.c
   (compiled against <brotli>/c/common/transform.c and context.c by the generator). */
#include <stdio.h>
#include "transform.c"
#include "context.c"

int main(int argc, char** argv) {
  const BrotliTransforms* t = BrotliGetTransforms();
  if (argc == 3) {
    /* dump-tables <dictionary.bin> <out>: every transform of the dictionary words 0, 1, 2, 3
       and 31 of each length 4 to 24, concatenated (the check in Codec/BrotliTests.lean). */
    static const int nd[25] = {0,0,0,0,10,10,11,11,10,10,10,10,10,9,9,8,7,7,8,7,7,6,6,5,5};
    static uint8_t dict[122784];
    static const int idxs[5] = {0, 1, 2, 3, 31};
    int off = 0;
    uint8_t buf[64];
    FILE* d = fopen(argv[1], "rb");
    FILE* f = fopen(argv[2], "wb");
    if (!d || !f || fread(dict, 1, sizeof dict, d) != sizeof dict) return 1;
    for (int len = 4; len <= 24; len++) {
      for (int j = 0; j < 5; j++)
        for (int tr = 0; tr < 121; tr++)
          fwrite(buf, 1, (size_t)BrotliTransformDictionaryWord(buf, dict + off + idxs[j] * len, len, t, tr), f);
      off += len << nd[len];
    }
    fclose(d);
    fclose(f);
    return 0;
  }
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
