/*
fx_emcc.c — the C entry points of the Emscripten baseline build of
lean/FxSubset.lean (experiments/wasm-components/baseline-emcc). The same
Lean code as the component; a char* ABI like formal/lean4/Wasm/l4_shim.c.

fx_parse_c answers "O<nquads>" or "E<message>"; fx_query_c answers the JSON
envelope. The caller frees the result with free().
*/
#include <lean/lean.h>
#include <emscripten.h>
#include <stdlib.h>
#include <string.h>

void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
extern lean_object *initialize_FxSubset(uint8_t builtin);
extern lean_object *fx_parse(lean_object *text, lean_object *format, lean_object *base);
extern lean_object *fx_query(lean_object *nquads, lean_object *sparql);

static int g_init = 0;
static void fx_init(void) {
    if (g_init) return;
    lean_initialize_runtime_module();
    lean_object *res = initialize_FxSubset(1);
    if (!lean_io_result_is_ok(res)) { lean_io_result_show_error(res); abort(); }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();
    g_init = 1;
}

/* A malloc'd copy of the Lean string s, after the prefix (0 or 1 bytes). */
static char *out(const char *prefix, lean_object *s) {
    size_t k = strlen(prefix), n = lean_string_size(s) - 1;
    char *p = malloc(k + n + 1);
    if (!p) abort();
    memcpy(p, prefix, k);
    memcpy(p + k, lean_string_cstr(s), n);
    p[k + n] = 0;
    return p;
}

EMSCRIPTEN_KEEPALIVE char *fx_parse_c(const char *text, const char *format, const char *base) {
    fx_init();
    lean_object *r = fx_parse(lean_mk_string(text), lean_mk_string(format), lean_mk_string(base));
    char *p = out(lean_obj_tag(r) == 1 ? "O" : "E", lean_ctor_get(r, 0));
    lean_dec(r);
    return p;
}

EMSCRIPTEN_KEEPALIVE char *fx_query_c(const char *nquads, const char *sparql) {
    fx_init();
    lean_object *r = fx_query(lean_mk_string(nquads), lean_mk_string(sparql));
    char *p = out("", r);
    lean_dec(r);
    return p;
}
