# Index bounded WebP image payloads

The frozen BBC News archive contains ten simple VP8 photographs and one extended VP8 image with an alpha chunk. Supporting those photos needs the lossy decoder. The project plan in [issue 1283](https://github.com/danbri/factoidal/issues/1283) starts with lossless decoding.

Both encodings use the same RIFF envelope. Index the compressed image, alpha and colour profile as bounded spans of the original byte array. Read both payload dimensions before any pixel allocation. The scanner advances through chunks without copying their payloads or retaining unknown chunks. It checks the RIFF limit, chunk padding and pixel budget and rejects animated inputs in this static entry point.

The proof concerns source-buffer bounds for a relative index in a returned span. Decoding compressed pixels and compositing animation frames are subsequent work. The browser does not select or paint WebP images from this change alone.

[RFC 9649](https://www.rfc-editor.org/rfc/rfc9649.html)

The lossless prefix-code layer follows RFC 9649 section 3.7.2.1. It checks alphabet sizes and complete canonical code space before using the shared Huffman table. A normal header's maximum length count is consumed per encoded token, including repeats. A singleton is represented by an in-range symbol and reads no bits. The executable guard cases exercise truncated, incomplete, oversubscribed and invalid simple codes.

A separate literal-only probe reads the five alphabets and agrees byte-for-byte with libwebp on three valid synthesized images. The fixtures cover singleton, simple pair and a normal table with a repeat token. They exercise the prefix reader through a WebP container. General LZ77, transforms, entropy images, color cache and browser integration are still open. BBC photos in the frozen set are VP8, which needs a separate decoder.
