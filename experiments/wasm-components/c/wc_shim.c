/* wc_shim.c — the C boundary of the experiment's Lean subset (WcCore.lean).
   Same three duties as formal/lean4/Wasm/l4_shim.c (initialise, convert
   strings, hand bytes out) and no RDF or SPARQL logic. Shared by every build
   of the experiment: the Emscripten baseline exports the wc_*_c functions
   directly, the component builds call them from wc_component.c.

   Ownership: the returned buffer is malloc'd here and owned by the caller
   (free it with wc_free); `*out_len` is its length in bytes, without NUL. */
#include <lean/lean.h>
#include <lean/mimalloc.h>
#include <stdlib.h>
#include <string.h>

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#define WC_EXPORT EMSCRIPTEN_KEEPALIVE
#else
#define WC_EXPORT
#endif

void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
lean_object *initialize_WcCore(uint8_t builtin);
lean_object *wc_turtle_to_nquads(lean_object *ttl, lean_object *base);
lean_object *wc_query_turtle(lean_object *ttl, lean_object *sparql);

static int g_init = 0;   /* 0 not yet, 1 ready, -1 failed */

WC_EXPORT int wc_init(void) {
    if (g_init) return g_init > 0;
    lean_initialize_runtime_module();
    lean_object *res = initialize_WcCore(1);
    if (lean_io_result_is_error(res)) {
        lean_io_result_show_error(res);
        lean_dec(res);
        g_init = -1;
        return 0;
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();
    g_init = 1;
    return 1;
}

static char *take(lean_object *s, size_t *out_len) {
    size_t n = lean_string_size(s) - 1;   /* lean_string_size counts the NUL */
    char *out = malloc(n + 1);
    if (out) { memcpy(out, lean_string_cstr(s), n + 1); *out_len = n; }
    lean_dec(s);
    return out;
}

WC_EXPORT char *wc_turtle_to_nquads_n(const char *ttl, size_t ttl_len,
                                      const char *base, size_t base_len,
                                      size_t *out_len) {
    if (!wc_init()) return NULL;
    return take(wc_turtle_to_nquads(lean_mk_string_from_bytes(ttl, ttl_len),
                                    lean_mk_string_from_bytes(base, base_len)), out_len);
}

WC_EXPORT char *wc_query_turtle_n(const char *ttl, size_t ttl_len,
                                  const char *sparql, size_t sparql_len,
                                  size_t *out_len) {
    if (!wc_init()) return NULL;
    return take(wc_query_turtle(lean_mk_string_from_bytes(ttl, ttl_len),
                                lean_mk_string_from_bytes(sparql, sparql_len)), out_len);
}

/* NUL-terminated forms, for the Emscripten baseline's ccall. */
WC_EXPORT char *wc_turtle_to_nquads_c(const char *ttl, const char *base) {
    size_t n;
    return wc_turtle_to_nquads_n(ttl, strlen(ttl), base, strlen(base), &n);
}

WC_EXPORT char *wc_query_turtle_c(const char *ttl, const char *sparql) {
    size_t n;
    return wc_query_turtle_n(ttl, strlen(ttl), sparql, strlen(sparql), &n);
}

WC_EXPORT void wc_free(char *p) { free(p); }
