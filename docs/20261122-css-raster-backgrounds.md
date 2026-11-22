# Raster CSS backgrounds

Issue [#704](https://github.com/danbri/factoidal-core/issues/704) tracks background images absent from actual Foafnaut pages and from WPT comparisons. Keep stylesheet URLs attached to their declarations, finish the cascade before choosing image requests, and use the existing bounded image transfer and bitmap store. The background bitmap IDs are assigned by the same store as HTML and SVG image IDs. Draw back to front over the colour, using the same image paint on the CPU and GPU.

The first candidate handles pure raster URL layer lists, automatic sizing, cover and contain, ordinary explicit sizes understood by the layout engine, and the ordinary repeat axes. It uses the default positioning area and clip. Other background position, origin and clip values, space and round repeats, canvas propagation, mixed gradient and raster layers, and dynamic resource discovery need further work. At most 4,096 tile primitives are emitted per box. A failed image leaves the other layers and colour visible.

Validation uses exact pinned WPT background-image-001 and -002 first, with background-image-cover-zoomed-1 as a separate sizing probe. Selection and native compilation checks are separate from the pixel measurements. No full-suite score is attributed to these focused cases.
