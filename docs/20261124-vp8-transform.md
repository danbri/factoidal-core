# VP8 inverse transforms

The VP8 reconstruction stage derives the six quantisation factors from the frame and segment, applies the signed-16-bit coefficient representation, then inverts the optional luma WHT and the 24 luma and chroma DCTs. The fold supplies residual samples in raster macroblock order for the predictor. A skipped macroblock requires only prediction and never transforms a block.

The Lean statements check the signed-16-bit bounds, preservation of already representable values and zero-input behaviour of both inverse transforms. The independent comparison samples the libwebp scalar inverse DCT before adding a predictor or clipping, after libwebp's own coefficient and WHT decoding. The comparison exercises the same archived BBC photos and split-partition inputs as the residual decoder.

Intra prediction, loop filtering, colour conversion and browser integration are separate remaining steps.
