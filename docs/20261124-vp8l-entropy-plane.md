# Decode a VP8L entropy-coded pixel plane

The plane decoder follows RFC 9649 sections 3.6 and 3.7. It reconstructs literal colours, overlapping backward references and cache tokens. A spatial entropy image can select groups independently across the main plane. Every returned pixel array carries its exact size and each source copy is checked before starting. The Lean theorem proves that scan-line distances are positive. The prefix reader also accepts a duplicate pair as a zero-bit singleton, as RFC 9649 permits.

Four complete, no-transform fixture images matched libwebp byte for byte. They cover an overlapping copy, a cache lookup, adjacent regions using different group tables and a duplicate simple code. A deliberately early backward reference is rejected. The plane decoder is the input to inverse transforms. The remaining transforms and browser integration are separate stages.
