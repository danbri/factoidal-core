#include <ft2build.h>
#include FT_FREETYPE_H
#include FT_OUTLINE_H
#include <stdio.h>
#include <stdlib.h>
static int mv(const FT_Vector*p,void*s){printf(" M %ld %ld",p->x,p->y);return 0;}
static int ln(const FT_Vector*p,void*s){printf(" L %ld %ld",p->x,p->y);return 0;}
static int cn(const FT_Vector*a,const FT_Vector*p,void*s){printf(" Q %ld %ld %ld %ld",a->x,a->y,p->x,p->y);return 0;}
static int cb(const FT_Vector*a,const FT_Vector*b,const FT_Vector*p,void*s){printf(" C %ld %ld %ld %ld %ld %ld",a->x,a->y,b->x,b->y,p->x,p->y);return 0;}
int main(int c,char**v){FT_Library l;FT_Face f;FT_Init_FreeType(&l);if(FT_New_Face(l,v[1],0,&f))return 1;int a=atoi(v[2]),b=atoi(v[3]);if(b>f->num_glyphs)b=f->num_glyphs;FT_Outline_Funcs fn={mv,ln,cn,cb,0,0};
for(int g=a;g<b;g++){printf("%d",g);if(!FT_Load_Glyph(f,g,FT_LOAD_NO_SCALE|FT_LOAD_NO_HINTING|FT_LOAD_NO_BITMAP)){FT_Outline_Decompose(&f->glyph->outline,&fn,0);}else printf(" ERR");puts("");}return 0;}
