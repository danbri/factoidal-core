/*
 * prelude_bytecode.c: compile tools/wasmvm/quickjs/prelude.js to QuickJS-NG bytecode at
 * guest build time (build-quickjs.sh), so that qjs_new reads bytecode (JS_ReadObject) and
 * does not parse 100 KB of source each time the guest module loads.
 *
 * Built natively from the same pinned QuickJS-NG sources as the guest. The bytecode
 * format is QuickJS-NG's own (JS_WriteObject, BC_VERSION checked on read); it holds no
 * pointers, and both the build host and wasm32 are little-endian.
 *
 *   prelude_bytecode PRELUDE.js OUT.h [NAME]
 * writes `static const uint8_t prelude_bc[]` and `prelude_bc_len`; with NAME, `NAME_bc[]` and `NAME_bc_len` (webassembly.js is
 * compiled the same way, as `wasm_glue`).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "quickjs.h"

int main(int argc, char **argv) {
  if (argc != 3 && argc != 4) { fprintf(stderr, "usage: prelude_bytecode PRELUDE.js OUT.h [NAME]\n"); return 2; }
  const char *name = argc == 4 ? argv[3] : "prelude";
  FILE *in = fopen(argv[1], "rb");
  if (!in) { perror(argv[1]); return 1; }
  fseek(in, 0, SEEK_END); long n = ftell(in); fseek(in, 0, SEEK_SET);
  char *src = malloc((size_t) n + 1);
  if (!src || fread(src, 1, (size_t) n, in) != (size_t) n) { fprintf(stderr, "read failed\n"); return 1; }
  src[n] = 0; fclose(in);
  JSRuntime *rt = JS_NewRuntime();
  JSContext *ctx = JS_NewContext(rt);
  JSValue f = JS_Eval(ctx, src, (size_t) n, "<foafnaut-prelude>", JS_EVAL_TYPE_GLOBAL | JS_EVAL_FLAG_COMPILE_ONLY);
  if (JS_IsException(f)) {
    JSValue e = JS_GetException(ctx);
    const char *m = JS_ToCString(ctx, e);
    fprintf(stderr, "prelude.js does not compile: %s\n", m ? m : "?");
    return 1;
  }
  size_t len = 0;
  /* No source text: a platform function's toString shows no prelude code, as in a browser. */
  uint8_t *bc = JS_WriteObject(ctx, &len, f, JS_WRITE_OBJ_BYTECODE | JS_WRITE_OBJ_STRIP_SOURCE);
  if (!bc) { fprintf(stderr, "JS_WriteObject failed\n"); return 1; }
  FILE *out = fopen(argv[2], "w");
  if (!out) { perror(argv[2]); return 1; }
  fprintf(out, "/* %s as QuickJS-NG bytecode (prelude_bytecode.c); %zu bytes. */\n", argv[1], len);
  fprintf(out, "static const uint8_t %s_bc[] = {", name);
  for (size_t i = 0; i < len; i++) fprintf(out, "%s%u,", i % 32 ? "" : "\n", bc[i]);
  fprintf(out, "\n};\nstatic const size_t %s_bc_len = %zu;\n", name, len);
  fclose(out);
  js_free(ctx, bc);
  JS_FreeValue(ctx, f); JS_FreeContext(ctx); JS_FreeRuntime(rt);
  return 0;
}
