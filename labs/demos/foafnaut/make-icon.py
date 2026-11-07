#!/usr/bin/env python3
"""Write the foafnaut app icon as a PNG: a small FOAF graph (three people and their
links) on a dark rounded square. Standard library only; build-executables.sh makes the
.icns from it with sips and iconutil. Usage: make-icon.py OUT.png [SIZE]"""
import math, struct, sys, zlib

def png(path, size, pixel):
    rows = []
    for y in range(size):
        row = bytearray([0])
        for x in range(size):
            row += bytes(pixel(x, y))
        rows.append(bytes(row))
    raw = zlib.compress(b"".join(rows), 9)
    def chunk(kind, data):
        return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data) & 0xffffffff)
    with open(path, "wb") as out:
        out.write(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 6, 0, 0, 0))
                  + chunk(b"IDAT", raw) + chunk(b"IEND", b""))

def segment_distance(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))

def main():
    out = sys.argv[1]
    size = int(sys.argv[2]) if len(sys.argv) > 2 else 1024
    s = size / 1024
    nodes = [(330 * s, 360 * s), (700 * s, 330 * s), (512 * s, 700 * s)]
    links = [(0, 1), (1, 2), (2, 0)]
    def cover(d):  # one pixel of anti-aliasing at the edge
        return max(0.0, min(1.0, 0.5 - d))
    def pixel(x, y):
        px, py = x + 0.5, y + 0.5
        # Rounded square, 100 units in from the edge as macOS icons are.
        m, r = 100 * s, 180 * s
        qx = max(abs(px - size / 2) - (size / 2 - m - r), 0)
        qy = max(abs(py - size / 2) - (size / 2 - m - r), 0)
        square = cover(math.hypot(qx, qy) - r)
        if square == 0:
            return (0, 0, 0, 0)
        shade = py / size
        color = [20 + 20 * shade, 28 + 24 * shade, 60 + 40 * shade]
        line = max(cover(segment_distance(px, py, *nodes[a], *nodes[b]) - 14 * s) for a, b in links)
        color = [c * (1 - line) + v * line for c, v in zip(color, (255, 196, 0))]
        dot = max(cover(math.hypot(px - nx, py - ny) - 82 * s) for nx, ny in nodes)
        color = [c * (1 - dot) + v * dot for c, v in zip(color, (224, 32, 138))]
        return (round(color[0]), round(color[1]), round(color[2]), round(255 * square))
    png(out, size, pixel)

main()
