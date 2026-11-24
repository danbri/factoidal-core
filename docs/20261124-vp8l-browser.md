# Decode static lossless WebP in browser image inputs

The bounded VP8L decoder applies every inverse transform in RFC 9649 section 3.5, then emits straight RGBA with a proved output size. It rejects duplicate transform declarations. Its picture bounds match the PNG limits.

Foafnaut's shared image decoder identifies RIFF WebP by its signature and uses this path for direct lossless resources, embedded images and tab icons. Source-set candidates keep their existing alternative-format behavior until lossy WebP or a fetch-time fallback can cover them. The image tests check pixels and dimensions, and the showcase test exercises a direct image and a tab icon.

Local differential testing decoded dozens of complete libwebp files byte for byte. Browser native and Wasm checks verify the production boundary independently.
