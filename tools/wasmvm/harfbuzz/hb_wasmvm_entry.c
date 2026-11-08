/*
 * hb_wasmvm_entry.c: the entry point of the HarfBuzz build that runs in the Lean
 * WasmVM engine (https://github.com/danbri/factoidal/issues/1244; record:
 * docs/designissues/2026-11-07-wasmvm-engine.md, "HarfBuzz in the VM").
 *
 * Built by tools/wasmvm/build-harfbuzz.sh into a standalone Wasm module (WASI
 * imports only, no JavaScript). Exports:
 *
 *   hbw_alloc(n) -> ptr          memory for the host to write a font or text into
 *   hbw_free(ptr)
 *   hbw_shape(font_ptr, font_len, text_ptr, text_len, out_ptr, out_cap) -> count
 *
 * hbw_shape shapes UTF-8 text with the font (face index 0), with the script,
 * direction and language guessed from the text (hb_buffer_guess_segment_properties,
 * as the hb-shape tool does), the font scale equal to units per em, and no features.
 * For each output glyph it writes 6 little-endian int32 values at out_ptr:
 *
 *   glyph id, cluster (byte offset in the text), x advance, y advance, x offset, y offset
 *
 * all in font units. It gives the number of glyphs, or a negative value:
 * -1 when the glyphs do not fit in out_cap records (nothing is written),
 * -2 when HarfBuzz could not allocate.
 *
 * The face and font are kept for the last (font_ptr, font_len), so shaping many
 * strings with one font loads the font once. The host must not change those bytes
 * while they are cached; a call with another pointer or length drops the cache.
 */
#include <stdint.h>
#include <stdlib.h>
#include "hb.h"

static const char *cached_ptr = 0;
static int32_t cached_len = -1;
static hb_font_t *cached_font = 0;

__attribute__((export_name("hbw_alloc")))
void *hbw_alloc(int32_t n) { return malloc((size_t) n); }

__attribute__((export_name("hbw_free")))
void hbw_free(void *p) { free(p); }

static hb_font_t *font_for(const char *font_ptr, int32_t font_len) {
  if (cached_font && cached_ptr == font_ptr && cached_len == font_len) return cached_font;
  if (cached_font) hb_font_destroy(cached_font);
  hb_blob_t *blob = hb_blob_create(font_ptr, (unsigned) font_len, HB_MEMORY_MODE_READONLY, 0, 0);
  hb_face_t *face = hb_face_create(blob, 0);
  hb_blob_destroy(blob);
  hb_font_t *font = hb_font_create(face);
  hb_face_destroy(face);
  cached_ptr = font_ptr;
  cached_len = font_len;
  cached_font = font;
  return font;
}

__attribute__((export_name("hbw_shape")))
int32_t hbw_shape(const char *font_ptr, int32_t font_len, const char *text_ptr, int32_t text_len,
                  int32_t *out, int32_t out_cap) {
  hb_font_t *font = font_for(font_ptr, font_len);
  hb_buffer_t *buf = hb_buffer_create();
  hb_buffer_add_utf8(buf, text_ptr, text_len, 0, text_len);
  hb_buffer_guess_segment_properties(buf);
  hb_shape(font, buf, 0, 0);
  if (!hb_buffer_allocation_successful(buf)) { hb_buffer_destroy(buf); return -2; }
  unsigned n = 0;
  hb_glyph_info_t *info = hb_buffer_get_glyph_infos(buf, &n);
  hb_glyph_position_t *pos = hb_buffer_get_glyph_positions(buf, &n);
  if ((int32_t) n > out_cap) { hb_buffer_destroy(buf); return -1; }
  for (unsigned i = 0; i < n; i++) {
    int32_t *r = out + 6 * i;
    r[0] = (int32_t) info[i].codepoint;
    r[1] = (int32_t) info[i].cluster;
    r[2] = pos[i].x_advance;
    r[3] = pos[i].y_advance;
    r[4] = pos[i].x_offset;
    r[5] = pos[i].y_offset;
  }
  hb_buffer_destroy(buf);
  return (int32_t) n;
}

/* A standalone module needs a main or --no-entry; this build uses --no-entry and
 * runs _initialize (the constructors) before the first call. */
