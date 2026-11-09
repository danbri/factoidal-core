#!/usr/bin/env python3
"""Reference pixels of colour emoji from an independent COLR renderer (issue 1276).

    uvx --from 'blackrenderer[skia]' --with uharfbuzz python labs/demos/foafnaut/emoji_reference.py

blackrenderer (https://github.com/BlackFoundryCom/black-renderer, Apache 2.0) reads COLR
and CPAL with fontTools and paints with Skia (skia-python); HarfBuzz (uharfbuzz) gives the
glyph of each sequence. Nothing here shares code with the engine. For each emoji below, the
glyph of the vendored Noto Color Emoji slice is drawn at the pixel size given, in the box the
engine uses (`ColrRaster.draw`): the clip box at `px / unitsPerEm`, rounded out to whole
pixels, y down. The PNG files and manifest.json go to fixtures/emoji-reference/;
emoji_pixels_test.ts compares the engine's pixels with them.
"""
import json, math, os
import uharfbuzz as hb
from fontTools.ttLib import TTFont
from blackrenderer.font import BlackRendererFont
from blackrenderer.backends.skia import SkiaPixelSurface

LAB = os.path.dirname(os.path.abspath(__file__))
FONTS = os.path.join(LAB, '..', '..', '..', 'third_party', 'fonts', 'noto-color-emoji')
OUT = os.path.join(LAB, 'fixtures', 'emoji-reference')
# (name, slice, text, pixels to the em): radial and linear gradients, transforms, the SRC_IN
# composite (lizard, mantelpiece clock), a skin tone, a ZWJ family, a flag, a keycap.
CASES = [
    ('grinning-32', 'Smileys', '\U0001F600', 32), ('grinning-64', 'Smileys', '\U0001F600', 64),
    ('hearts-64', 'Smileys', '\U0001F970', 64), ('thumbs-tone3-48', 'People', '\U0001F44D\U0001F3FD', 48),
    ('family-48', 'PeopleZWJ', '\U0001F468‍\U0001F469‍\U0001F467‍\U0001F466', 48),
    ('lizard-64', 'Animals', '\U0001F98E', 64), ('clock-64', 'Travel', '\U0001F570', 64),
    ('rainbow-32', 'Travel', '\U0001F308', 32), ('pizza-40', 'Food', '\U0001F355', 40),
    ('flag-gb-48', 'FlagsFK', '\U0001F1EC\U0001F1E7', 48), ('keycap-1-32', 'Symbols', '1️⃣', 32),
    ('grinning-128', 'Smileys', '\U0001F600', 128),
]

def main():
    os.makedirs(OUT, exist_ok=True)
    manifest = []
    for name, stem, text, px in CASES:
        path = os.path.join(FONTS, f'NotoColorEmoji-{stem}.ttf')
        face = hb.Face(hb.Blob.from_file_path(path))
        buf = hb.Buffer()
        buf.add_str(text)
        buf.guess_segment_properties()
        hb.shape(hb.Font(face), buf, {})
        glyphs = [g.codepoint for g in buf.glyph_infos]
        tt = TTFont(path, lazy=True)
        names = tt.getGlyphOrder()
        # Shaping hides U+FE0F at no width; the colour glyph is the one in the ClipList.
        clips = tt['COLR'].table.ClipList.clips
        gid = next(g for g in glyphs if names[g] in clips)
        clip = clips[names[gid]]
        upem = tt['head'].unitsPerEm
        s = px / upem
        ox, oy = math.floor(clip.xMin * s), math.floor(-clip.yMax * s)
        w, h = math.ceil(clip.xMax * s) - ox, math.ceil(-clip.yMin * s) - oy
        font = BlackRendererFont(path)
        surface = SkiaPixelSurface()
        # The surface's box is in y-up pixels: device x = X - ox, device y = -Y - oy.
        with surface.canvas((ox, -oy - h, ox + w, -oy)) as canvas:
            canvas.scale(s)
            font.drawGlyph(names[gid], canvas, palette=font.getPalette(0))
        surface.saveImage(os.path.join(OUT, name + '.png'))
        manifest.append({'name': name, 'font': f'noto-color-emoji/NotoColorEmoji-{stem}.ttf', 'text': text,
                         'px': px, 'glyph': gid, 'width': w, 'height': h, 'left': ox, 'top': oy})
        print(name, names[gid], w, h, ox, oy)
    with open(os.path.join(OUT, 'manifest.json'), 'w') as f:
        json.dump(manifest, f, indent=1, ensure_ascii=False)
        f.write('\n')

if __name__ == '__main__':
    main()
