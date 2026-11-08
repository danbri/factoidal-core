#!/usr/bin/env python3
"""Write the small PNG files of the Images demo page (pages/showcase-images.html).

The pictures are drawn here, pixel by pixel, so the repository holds the program that
makes them. Python's standard library only. Run it again after a change; the output is
the same bytes each time.

- images-landscape.png: 160 by 96, RGB: sky, sun and two hills.
- images-badge.png: 48 by 48, RGBA: a ring with a transparent outside and centre.
"""
import math
import os
import struct
import zlib

PAGES = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'pages')


def png(width, height, rows, alpha):
    """A PNG file (ISO/IEC 15948) of 8-bit RGB or RGBA rows, filter type 0."""
    def chunk(kind, data):
        return struct.pack('>I', len(data)) + kind + data + struct.pack('>I', zlib.crc32(kind + data) & 0xffffffff)
    raw = b''.join(b'\0' + bytes(row) for row in rows)
    header = struct.pack('>IIBBBBB', width, height, 8, 6 if alpha else 2, 0, 0, 0)
    return b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', header) + chunk(b'IDAT', zlib.compress(raw, 9)) + chunk(b'IEND', b'')


def landscape():
    width, height = 160, 96
    rows = []
    for y in range(height):
        row = []
        for x in range(width):
            # Sky from deep blue at the top to pale at the horizon.
            t = y / height
            r, g, b = int(40 + 150 * t), int(90 + 130 * t), int(200 + 50 * t)
            if (x - 118) ** 2 + (y - 26) ** 2 <= 13 ** 2:
                r, g, b = 255, 214, 64
            far = 60 + 10 * math.sin(x / 17.0)
            near = 74 + 8 * math.sin(x / 11.0 + 2)
            if y >= far:
                r, g, b = 70, 130, 80
            if y >= near:
                r, g, b = 40, 100 + (x * 3) % 20, 50
            row += [r, g, b]
        rows.append(row)
    return png(width, height, rows, False)


def badge():
    size = 48
    rows = []
    for y in range(size):
        row = []
        for x in range(size):
            d = math.hypot(x + 0.5 - 24, y + 0.5 - 24)
            if 12 <= d <= 22:
                row += [160, 24, 106, 255]
            elif 10 <= d < 12 or 22 < d <= 23:
                row += [160, 24, 106, 128]
            else:
                row += [0, 0, 0, 0]
        rows.append(row)
    return png(size, size, rows, True)


for name, data in [('images-landscape.png', landscape()), ('images-badge.png', badge())]:
    with open(os.path.join(PAGES, name), 'wb') as out:
        out.write(data)
    print(name, len(data), 'bytes')
