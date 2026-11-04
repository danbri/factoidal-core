#ifndef NATIVE_COORDINATES_H
#define NATIVE_COORDINATES_H

typedef struct { double x, y; } NGPoint;

// NGView is flipped: its local +Y already points down, like the framebuffer.
// Use the backing rectangle's dimensions, not its coordinate-system origin or
// orientation. In our layer-hosting view convertPointToBacking negates local Y.
// Keep out-of-bounds coordinates signed so a drag can leave the view; abs/clamp
// here would turn an outside pointer into a false hit inside the scene.
static inline NGPoint ng_framebuffer_point(NGPoint local, NGPoint boundsOrigin,
                                           NGPoint boundsSize, NGPoint backingSize) {
  if (boundsSize.x <= 0 || boundsSize.y <= 0) return (NGPoint){-1, -1};
  return (NGPoint){
    (local.x - boundsOrigin.x) * backingSize.x / boundsSize.x,
    (local.y - boundsOrigin.y) * backingSize.y / boundsSize.y
  };
}

#endif
