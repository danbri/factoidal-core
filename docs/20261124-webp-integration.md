# Static WebP in Foafnaut

The browser image loader dispatches both static WebP bitstreams from the same checked container header. Header-only dimensions feed layout. A WebP candidate may be selected in `picture` or `srcset`, and static WebP uses the existing bitmap paths for HTML and SVG images, CSS backgrounds, image embeds and icons.

Lossy WebP follows the VP8 loop filter and colour conversion and decodes its own alpha if present. Raw alpha and headerless VP8L-coded alpha share the four WebP prediction modes. Reserved bits and preprocessing hints are ignored. `alphaAdd_mod256` states the wrapping rule for alpha residuals.

The exact codec comparison uses the archived BBC photos and two alpha compression modes across all four predictors. Browser checks compare native paint against PNG equivalents. Animated WebP and ICC profile conversion remain open.
