/* wc_component.c — the WIT exports of world `engine`
   (wit/factoidal.wit) over wc_shim.c, for wit-bindgen's C bindings
   (engine.h, generated at build time). Canonical ABI ownership: the
   argument strings are owned by this function and freed here; the result
   strings are malloc'd and freed by the generated post-return function. */
#include "engine.h"
#include <stdlib.h>
#include <string.h>

char *wc_turtle_to_nquads_n(const char *, size_t, const char *, size_t, size_t *);
char *wc_query_turtle_n(const char *, size_t, const char *, size_t, size_t *);

static void set(engine_string_t *s, char *buf, size_t n) {
    s->ptr = (uint8_t *)buf;
    s->len = n;
}

bool exports_factoidal_core_rdf_turtle_to_nquads(engine_string_t *turtle,
        engine_string_t *maybe_base, engine_string_t *ret, engine_string_t *err) {
    size_t n = 0;
    char *out = wc_turtle_to_nquads_n((const char *)turtle->ptr, turtle->len,
        maybe_base ? (const char *)maybe_base->ptr : "",
        maybe_base ? maybe_base->len : 0, &n);
    engine_string_free(turtle);
    if (maybe_base) engine_string_free(maybe_base);
    if (!out) { engine_string_dup(err, "engine initialisation failed"); return false; }
    if (n > 0 && out[0] == '!') {          /* WcCore.turtleToNQuadsC error mark */
        memmove(out, out + 1, n);          /* moves the NUL too */
        set(err, out, n - 1);
        return false;
    }
    set(ret, out, n);
    return true;
}

void exports_factoidal_core_rdf_query(engine_string_t *turtle,
        engine_string_t *sparql, engine_string_t *ret) {
    size_t n = 0;
    char *out = wc_query_turtle_n((const char *)turtle->ptr, turtle->len,
        (const char *)sparql->ptr, sparql->len, &n);
    engine_string_free(turtle);
    engine_string_free(sparql);
    if (!out) { engine_string_dup(ret, "{\"ok\":false,\"error\":\"engine initialisation failed\"}"); return; }
    set(ret, out, n);
}
