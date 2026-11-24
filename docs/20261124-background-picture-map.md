# Reuse the background picture map across the style pass

Native samples of the frozen mobile US Wikipedia document showed the picture-map builder under the indexed body of `attachBackgrounds`. The current picture lookup helper returns a function of element ID. Eta-expansion can put the construction of its lookup table inside the indexed style pass, even though the map builder itself is not inlined. With bitmap font, this call chain accounted for 686 of 1,219 main-thread samples with engine leaf frames in one five-second sample. Those call graph counts describe the sample window, not whole-page elapsed time. The BBC News homepage also hit the same path.

Build the map at the call boundary and pass it as data to a non-inlined style pass. The equivalence theorem states equality of the resulting style array to using the original per-ID function. It covers the chosen bitmap, intrinsic size and unchanged styles for missing pictures. Native profiling and a paired frozen replay are separate checks for the runtime effect.

Related to [desktop acceptance](https://github.com/danbri/factoidal-core/issues/712).
