# Read the control prefix of lossy WebP

The frozen BBC home page contains eleven VP8 pictures. The new key-frame reader consumes only the flagged first partition, decodes the segmentation, filter and quantizer fields and indexes every coefficient partition without copying it. Each returned span carries its source bound. The Lean theorem gives the positive subinterval bounds for a boolean split. The code follows RFC 6386 sections 7, 9 and 19.2.

The differential compares the decoded fields with libwebp's webpinfo output on all eleven archived BBC pictures and checks a synthetic four-partition file produced by libvpx. It also verifies the partition size table. The reader ends after refresh-entropy-probs and returns that cursor so later code can read probability updates and macroblocks. It does not yet reconstruct any pixels.
