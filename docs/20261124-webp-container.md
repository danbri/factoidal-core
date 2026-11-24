# Index bounded WebP image payloads

The frozen BBC News archive contains ten simple VP8 photographs and one extended VP8 image with an alpha chunk. Supporting those photos needs the lossy decoder. The project plan in [issue 1283](https://github.com/danbri/factoidal/issues/1283) starts with lossless decoding.

Both encodings use the same RIFF envelope. Index the compressed image, alpha and colour profile as bounded spans of the original byte array. Read both payload dimensions before any pixel allocation. The scanner advances through chunks without copying their payloads or retaining unknown chunks. It checks the RIFF limit, chunk padding and pixel budget and rejects animated inputs in this static entry point.

The proof concerns source-buffer bounds for a relative index in a returned span. Decoding compressed pixels and compositing animation frames are subsequent work. The browser does not select or paint WebP images from this change alone.

[RFC 9649](https://www.rfc-editor.org/rfc/rfc9649.html)
