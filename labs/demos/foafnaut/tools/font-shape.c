/* Native font DATA adapter. HarfBuzz shapes one run in font units; FreeType
 * supplies exact outline commands and optional grayscale glyph coverage.
 * No CSS, line breaking, DOM traversal or document layout occurs here. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <math.h>
#include <hb.h>
#include <hb-ot.h>
#include <ft2build.h>
#include FT_FREETYPE_H
#include FT_OUTLINE_H
#ifdef __APPLE__
#include <CommonCrypto/CommonDigest.h>
#else
#include <openssl/sha.h>
#endif

static int fail(const char *s) { fprintf(stderr,"font-shape: %s\n",s); return 1; }
static void quoted(const char *s) {
  putchar('"');
  for (const unsigned char *p=(const unsigned char *)(s?s:""); *p; ++p) {
    switch (*p) {
      case '"': fputs("\\\"",stdout); break;
      case '\\': fputs("\\\\",stdout); break;
      case '\n': fputs("\\n",stdout); break;
      case '\r': fputs("\\r",stdout); break;
      case '\t': fputs("\\t",stdout); break;
      default: if (*p<32) printf("\\u%04x",*p); else putchar(*p);
    }
  }
  putchar('"');
}
static int valid_utf8(const unsigned char *s) {
  while (*s) {
    uint32_t c; unsigned n;
    if (*s<128) { ++s; continue; }
    if (*s>=0xc2 && *s<=0xdf) { c=*s&31; n=1; }
    else if (*s>=0xe0 && *s<=0xef) { c=*s&15; n=2; }
    else if (*s>=0xf0 && *s<=0xf4) { c=*s&7; n=3; }
    else return 0;
    unsigned count=n; ++s;
    while (n--) { if ((*s&0xc0)!=0x80) return 0; c=(c<<6)|(*s++&63); }
    if ((count==1 && c<128)||(count==2 && c<2048)||(count==3 && c<65536)||
        c>0x10ffff||(c>=0xd800&&c<=0xdfff)) return 0;
  }
  return 1;
}
typedef struct { int first; int contour; } OutlineState;
static void separator(OutlineState *s) { if (!s->first) putchar(','); s->first=0; }
static int move_to(const FT_Vector *p,void *state) {
  OutlineState *s=state;
  if(s->contour) { separator(s); fputs("[\"Z\"]",stdout); }
  separator(s); printf("[\"M\",%ld,%ld]",p->x,p->y); s->contour=1; return 0;
}
static int line_to(const FT_Vector *p,void *state) {
  separator(state); printf("[\"L\",%ld,%ld]",p->x,p->y); return 0;
}
static int conic_to(const FT_Vector *a,const FT_Vector *p,void *state) {
  separator(state); printf("[\"Q\",%ld,%ld,%ld,%ld]",a->x,a->y,p->x,p->y); return 0;
}
static int cubic_to(const FT_Vector *a,const FT_Vector *b,const FT_Vector *p,void *state) {
  separator(state); printf("[\"C\",%ld,%ld,%ld,%ld,%ld,%ld]",a->x,a->y,b->x,b->y,p->x,p->y); return 0;
}
static void sha256(const unsigned char *p,unsigned n,char out[65]) {
  unsigned char digest[32];
#ifdef __APPLE__
  CC_SHA256(p,n,digest);
#else
  SHA256(p,n,digest);
#endif
  for(unsigned i=0;i<32;++i) sprintf(out+i*2,"%02x",digest[i]);
  out[64]=0;
}
static int positive_size(const char *s,unsigned *out) {
  if(!*s) return 0;
  errno=0; char *end; unsigned long n=strtoul(s,&end,10);
  if(errno || *end || n<1 || n>512 || *s=='-') return 0;
  *out=(unsigned)n; return 1;
}
int main(int argc,char **argv) {
  if(argc!=4 && argc!=5) return fail("usage: font-shape FONT_FILE UTF8_TEXT PIXEL_SIZE [FACE_INDEX]");
  unsigned px;
  if(!positive_size(argv[3],&px)) return fail("pixel size must be an integer from1 through512");
  if(strlen(argv[2])>65536 || !valid_utf8((const unsigned char *)argv[2]))
    return fail("text must be valid UTF-8 and at most65536 bytes");
  unsigned face_index=0;
  if(argc==5) {
    errno=0; char *end; unsigned long n=strtoul(argv[4],&end,10);
    if(errno || !*argv[4] || *end || *argv[4]=='-' || n>65535) return fail("invalid face index");
    face_index=(unsigned)n;
  }
  hb_blob_t *blob=hb_blob_create_from_file_or_fail(argv[1]);
  if(!blob) return fail("cannot read font file");
  unsigned font_bytes=0; const char *font_data=hb_blob_get_data(blob,&font_bytes);
  if(font_bytes==0 || font_bytes>134217728) return fail("font must contain1 to134217728 bytes");
  char digest[65]; sha256((const unsigned char *)font_data,font_bytes,digest);
  FT_Library library; FT_Face face;
  if(FT_Init_FreeType(&library)) return fail("FreeType initialization failed");
  if(FT_New_Memory_Face(library,(const FT_Byte *)font_data,font_bytes,face_index,&face))
    return fail("FreeType rejected font or face index");
  if(!FT_IS_SCALABLE(face) || face->units_per_EM==0) return fail("scalable font required");
  hb_face_t *hface=hb_face_create(blob,face_index);
  hb_font_t *font=hb_font_create(hface);
  hb_ot_font_set_funcs(font);
  unsigned upem=hb_face_get_upem(hface);
  if(upem!=face->units_per_EM) return fail("HarfBuzz and FreeType units-per-em disagree");
  hb_font_set_scale(font,(int)upem,(int)upem);
  hb_buffer_t *buffer=hb_buffer_create();
  hb_buffer_set_cluster_level(buffer,HB_BUFFER_CLUSTER_LEVEL_MONOTONE_GRAPHEMES);
  hb_buffer_add_utf8(buffer,argv[2],-1,0,-1);
  hb_buffer_guess_segment_properties(buffer);
  hb_shape(font,buffer,NULL,0);
  if(!hb_buffer_allocation_successful(buffer)) return fail("HarfBuzz allocation failed");
  unsigned count; hb_glyph_info_t *infos=hb_buffer_get_glyph_infos(buffer,&count);
  hb_glyph_position_t *positions=hb_buffer_get_glyph_positions(buffer,NULL);
  if(count>65536) return fail("shaped run exceeds65536 glyphs");
  /* Validate all unique glyph loads before writing any JSON. */
  unsigned char *seen=calloc((size_t)face->num_glyphs,1);
  if(!seen) return fail("glyph index allocation failed");
  uint64_t total_points=0;
  for(unsigned i=0;i<count;++i) {
    unsigned id=infos[i].codepoint;
    if(id>=(unsigned)face->num_glyphs) return fail("shaper returned out-of-range glyph");
    if(!seen[id]) {
      if(FT_Load_Glyph(face,id,FT_LOAD_NO_SCALE|FT_LOAD_NO_HINTING|FT_LOAD_NO_BITMAP))
        return fail("FreeType could not load outline");
      if(face->glyph->format!=FT_GLYPH_FORMAT_OUTLINE) return fail("non-outline glyph unsupported");
      if(FT_Outline_Check(&face->glyph->outline)) return fail("invalid glyph outline");
      /* v1 transports nonzero contour geometry, not an outline fill-rule tag.
       * Refuse a different rule before any JSON instead of changing its fill. */
      if(face->glyph->outline.flags & FT_OUTLINE_EVEN_ODD_FILL)
        return fail("even-odd font outline fill unsupported by font-data-v1");
      total_points+=(unsigned)face->glyph->outline.n_points;
      if(total_points>1048576) return fail("run exceeds1048576 outline points");
      seen[id]=1;
    }
  }
  /* Bound raster output before emitting JSON, even for large Unicode runs. */
  if(FT_Set_Pixel_Sizes(face,0,px)) return fail("FreeType rejected pixel size");
  uint64_t bitmap_pixels=0;
  for(unsigned id=0;id<(unsigned)face->num_glyphs;++id) if(seen[id]) {
    if(FT_Load_Glyph(face,id,FT_LOAD_NO_HINTING|FT_LOAD_NO_BITMAP) || FT_Render_Glyph(face->glyph,FT_RENDER_MODE_NORMAL))
      return fail("glyph rasterization failed");
    FT_Bitmap *b=&face->glyph->bitmap;
    if(b->width && b->rows && b->pixel_mode!=FT_PIXEL_MODE_GRAY) return fail("non-grayscale glyph bitmap unsupported");
    bitmap_pixels+=(uint64_t)b->width*b->rows;
    if(bitmap_pixels>16777216) return fail("run exceeds16777216 bitmap pixels");
  }
  int major,minor,patch; FT_Library_Version(library,&major,&minor,&patch);
  fputs("{\"schema\":\"factoidal-font-data-v1\",\"fontPath\":",stdout); quoted(argv[1]);
  printf(",\"fontSha256\":\"%s\",\"fontBytes\":%u,\"faceIndex\":%u,\"family\":",digest,font_bytes,face_index);
  quoted(face->family_name); fputs(",\"style\":",stdout); quoted(face->style_name);
  printf(",\"unitsPerEm\":%u,\"ascender\":%d,\"descender\":%d,\"lineGap\":%d",upem,face->ascender,face->descender,face->height-face->ascender+face->descender);
  fputs(",\"coordinateSystem\":\"font units, positive y up\",\"clusterUnits\":\"UTF-8 byte offsets\",\"text\":",stdout); quoted(argv[2]);
  fputs(",\"direction\":",stdout); quoted(hb_direction_to_string(hb_buffer_get_direction(buffer)));
  char script[5]={0}; hb_tag_to_string(hb_script_to_iso15924_tag(hb_buffer_get_script(buffer)),script);
  fputs(",\"script\":",stdout); quoted(script);
  fputs(",\"language\":",stdout); quoted(hb_language_to_string(hb_buffer_get_language(buffer)));
  printf(",\"harfbuzzVersion\":\"%s\",\"freeTypeVersion\":\"%d.%d.%d\",\"bitmapPixelSize\":%u",hb_version_string(),major,minor,patch,px);
  fputs(",\"rasterMode\":\"FreeType normal grayscale, no hinting, no embedded bitmap\",\"glyphs\":[",stdout);
  for(unsigned i=0;i<count;++i) {
    if(i) putchar(',');
    printf("{\"id\":%u,\"cluster\":%u,\"xAdvance\":%d,\"yAdvance\":%d,\"xOffset\":%d,\"yOffset\":%d}",
      infos[i].codepoint,infos[i].cluster,positions[i].x_advance,positions[i].y_advance,positions[i].x_offset,positions[i].y_offset);
  }
  fputs("],\"outlines\":[",stdout); int first=1;
  FT_Outline_Funcs funcs={move_to,line_to,conic_to,cubic_to,0,0};
  for(unsigned id=0;id<(unsigned)face->num_glyphs;++id) if(seen[id]) {
    if(!first) putchar(','); first=0;
    if(FT_Load_Glyph(face,id,FT_LOAD_NO_SCALE|FT_LOAD_NO_HINTING|FT_LOAD_NO_BITMAP)) return fail("outline reload failed");
    printf("{\"id\":%u,\"commands\":[",id);
    OutlineState state={1,0};
    if(FT_Outline_Decompose(&face->glyph->outline,&funcs,&state)) return fail("outline decomposition failed");
    if(state.contour) { separator(&state); fputs("[\"Z\"]",stdout); }
    fputs("]}",stdout);
  }
  fputs("],\"bitmaps\":[",stdout); first=1;
  if(FT_Set_Pixel_Sizes(face,0,px)) return fail("FreeType rejected pixel size");
  for(unsigned id=0;id<(unsigned)face->num_glyphs;++id) if(seen[id]) {
    if(FT_Load_Glyph(face,id,FT_LOAD_NO_HINTING|FT_LOAD_NO_BITMAP) || FT_Render_Glyph(face->glyph,FT_RENDER_MODE_NORMAL))
      return fail("glyph rasterization failed");
    FT_Bitmap *b=&face->glyph->bitmap;
    if(b->width && b->rows && b->pixel_mode!=FT_PIXEL_MODE_GRAY) return fail("non-grayscale glyph bitmap unsupported");
    if(!first) putchar(','); first=0;
    printf("{\"id\":%u,\"pixelSize\":%u,\"width\":%u,\"height\":%u,\"left\":%d,\"top\":%d,\"alpha\":[",id,px,b->width,b->rows,face->glyph->bitmap_left,face->glyph->bitmap_top);
    for(unsigned row=0;row<b->rows;++row) for(unsigned col=0;col<b->width;++col) {
      if(row||col) putchar(',');
      const unsigned char *data=b->pitch>=0?b->buffer+(size_t)row*(unsigned)b->pitch:
        b->buffer+(size_t)(b->rows-1-row)*(unsigned)(-b->pitch);
      unsigned value=data[col];
      if(b->num_grays>1 && b->num_grays!=256) value=value*255/(b->num_grays-1);
      printf("%u",value);
    }
    fputs("]}",stdout);
  }
  fputs("]}\n",stdout);
  free(seen); hb_buffer_destroy(buffer); hb_font_destroy(font); hb_face_destroy(hface);
  FT_Done_Face(face); FT_Done_FreeType(library); hb_blob_destroy(blob);
  return ferror(stdout)?1:0;
}
