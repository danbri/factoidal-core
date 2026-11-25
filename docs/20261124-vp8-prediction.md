# VP8 prediction records for WebP

The BBC news capture linked from [the everyday-site tracker](https://github.com/danbri/factoidal-core/issues/712) contains eleven lossy WebP photos. After the bounded control-prefix reader, lossy decoding needs the keyframe coefficient probabilities and intra prediction mode for each macroblock in raster order. This stage provides both using the control span and continuation from the existing parser. It adds no decode work to the browser path yet.

`coefficientIndex_injective` proves that distinct block types, frequency bands, previous-coefficient contexts or tree nodes select different entries. The index is bounded by its type and `Entropy.probability` accesses that exact entry. `macroblockGrid_capacity` proves that the number of prediction records is bounded by the number of source pixels, whose limit the WebP reader already checks. The returned prediction grid also carries an exact record count. These facts leave the arithmetic parser's full semantic correctness open.

The differential check compares the complete table, skip probability and every prediction record with libwebp 1.6.0. Residual decoding, reconstruction, filtering, RGB conversion and rendering are later steps.
