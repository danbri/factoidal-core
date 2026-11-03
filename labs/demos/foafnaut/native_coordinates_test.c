#include "native_coordinates.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static unsigned checks;
static void check(const char *label, NGPoint local, NGPoint origin, NGPoint size,
                  NGPoint backing, NGPoint expected) {
  NGPoint actual=ng_framebuffer_point(local,origin,size,backing);
  if (fabs(actual.x-expected.x)>0.000001 || fabs(actual.y-expected.y)>0.000001) {
    fprintf(stderr,"FAIL %s: (%g,%g), expected (%g,%g)\n",
      label,actual.x,actual.y,expected.x,expected.y);
    exit(1);
  }
  checks++;
}
int main(void) {
  NGPoint origin={0,0}, size={768,512}, retina={1536,1024};
  // Captured 2026-10-30 in the real M1 Terminal run. The old Cocoa point
  // conversion produced a negative Y for each of these inside-view clicks.
  check("layout trace",(NGPoint){223.7,203.4},origin,size,retina,(NGPoint){447.4,406.8});
  check("spring trace",(NGPoint){382.9,115.3},origin,size,retina,(NGPoint){765.8,230.6});
  check("vector handle trace",(NGPoint){185.9,64.1},origin,size,retina,(NGPoint){371.8,128.2});
  check("resized layout trace",(NGPoint){350.2,328.5},origin,(NGPoint){467,445},
    (NGPoint){934,890},(NGPoint){700.4,657});
  check("top left",origin,origin,size,retina,origin);
  check("bottom right",size,origin,size,retina,retina);
  check("1x display",(NGPoint){208,208},origin,size,size,(NGPoint){208,208});
  check("fractional backing scale",(NGPoint){208,208},origin,size,
    (NGPoint){1152,768},(NGPoint){312,312});
  check("bounds origin",(NGPoint){218,228},(NGPoint){10,20},size,retina,(NGPoint){416,416});
  check("drag outside above/left",(NGPoint){-10,-20},origin,size,retina,(NGPoint){-20,-40});
  check("drag outside below/right",(NGPoint){800,550},origin,size,retina,(NGPoint){1600,1100});
  check("empty view",origin,origin,(NGPoint){0,0},retina,(NGPoint){-1,-1});
  printf("Native framebuffer coordinate checks: %u passed\n",checks);
  return 0;
}
