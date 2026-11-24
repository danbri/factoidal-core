#!/usr/bin/env python3
"""Print the Brotli test vectors of formal/lean4/L4Factoidal/Codec/BrotliTests.lean.

Each vector is a stream written by the Python `brotli` package (libbrotli; version printed
in the output), with the size and SHA-256 of the input it was made from. Run:

    pip install brotli
    python3 tools/brotli/brotli_vectors.py
"""
import hashlib
import brotli

TEXT = (b"The quick brown fox jumps over the lazy dog. Those who cannot remember the past "
        b"are condemned to repeat it. In the beginning was the word, and the word was with "
        b"the people of the world; this is the information that the government provides.")


def cases():
    yield "empty_q0", b"", dict(quality=0)
    yield "empty_q11", b"", dict(quality=11)
    yield "hello_q11", b"hello", dict(quality=11)
    yield "text_q0", TEXT, dict(quality=0)
    yield "text_q5", TEXT, dict(quality=5)
    yield "text_q11", TEXT, dict(quality=11, mode=brotli.MODE_TEXT)
    rep = b"".join(b"line %d of a repetitive input\n" % (i % 50) for i in range(3000))
    yield "repeat_q5_w16", rep, dict(quality=5, lgwin=16)
    yield "repeat_q11_w10", rep, dict(quality=11, lgwin=10)
    # bytes that do not compress: the encoder writes an uncompressed meta-block
    noise = b"".join(hashlib.sha256(b"%d" % i).digest() for i in range(20))
    yield "noise_q5", noise, dict(quality=5)


def lean_bytes(b: bytes) -> str:
    rows = []
    for i in range(0, len(b), 16):
        rows.append("  " + ", ".join("0x%02x" % x for x in b[i:i + 16]))
    return "bytes [\n" + ",\n".join(rows) + " ]" if b else "bytes []"


def main():
    print("-- brotli (Python package) %s" % brotli.__version__)
    for name, data, opts in cases():
        c = brotli.compress(data, **opts)
        assert brotli.decompress(c) == data
        print("private def v_%s : ByteArray := %s" % (name, lean_bytes(c)))
        print("-- %s: %d bytes from %r, sha256 %s" % (name, len(data), opts, hashlib.sha256(data).hexdigest()))
        print("#guard (decompress v_%s (1 <<< 24)).toOption.map (fun o => (o.size, bytesToHex (sha256 o))) ==" % name)
        print("  some (%d, \"%s\")" % (len(data), hashlib.sha256(data).hexdigest()))
        print()


if __name__ == "__main__":
    main()
