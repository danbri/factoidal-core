# Media test clips

Small audio and video files for the Ogg and WebM readers and the decoders that run in
WasmVM (`formal/lean4/L4Factoidal/Media/`; record:
`docs/designissues/2026-11-08-media-wasmvm.md`).

The first four files were made for this repository on 2026-11-08 with FFmpeg 9.0.1 (Homebrew),
from FFmpeg's own signal generators: no third-party picture or sound is in them.
Licence: CC0 1.0 (https://creativecommons.org/publicdomain/zero/1.0/).

| File | Content | Bytes | SHA-256 |
|---|---|---|---|
| `arpeggio.opus` | Ogg Opus, 48 kHz stereo, 4 s, 24 kbit/s | 21405 | `bcda305459d3790dbcd063b2eab5d1c0bb66b5a7d72a4d808c9bec7121ee2755` |
| `arpeggio.ogg` | Ogg Vorbis, 44.1 kHz stereo, 4 s | 16085 | `583c4a6ac7f82b55e6508971f3438386a2fdb93c61e3de9bdb83f3410e99fa2c` |
| `testsrc-320x180.webm` | WebM, VP8 320x180 24 fps and Opus 48 kHz stereo, 2 s | 86862 | `403c407843d71bc92a768f1fbfbf0c19b7adf1adfbb173f21a9a34a948b459fd` |
| `testsrc-160x90.webm` | WebM, VP8 160x90 24 fps and Vorbis 44.1 kHz stereo, 2 s | 42125 | `2f8769fbed5350d67e5a19fc4617d1c4e9a72642057491270c539348ae61db5d` |
| `arpeggio-cbr128.mp3` | MP3 (MPEG-1 layer III), 44.1 kHz stereo, 128 kbit/s CBR with a LAME Info header, 4 s | 65200 | `5ed490e482f8c197c4abc4de8d05f8c23e1bdecdc0f0ae36c3826ba363008f27` |
| `arpeggio-vbr.mp3` | MP3, 44.1 kHz stereo, VBR (`-V 2`) with a Xing/LAME header, 4 s | 41724 | `07fbf628a6d4cb7c99d366f337350c8468c573f873f4155aee5f06b73010aecc` |
| `arpeggio-mono22.mp3` | MP3 (MPEG-2 layer III), 22.05 kHz mono, 48 kbit/s, 4 s | 24450 | `f073857519e44b45ba1f7af83573a45428ac0651358d7f83e3a92bc782f78dca` |

The sound is a C major arpeggio (C4, E4, G4, C5, a quarter second each, each note with
a half-sine envelope; the right channel at 0.7 of the left). The picture is FFmpeg's
`testsrc2` pattern (colour bars, a moving gradient, a running time code).

Commands (zsh; `A` is the sound):

    F='261.63*eq(mod(floor(t*4)\,4)\,0)+329.63*eq(mod(floor(t*4)\,4)\,1)+392*eq(mod(floor(t*4)\,4)\,2)+523.25*eq(mod(floor(t*4)\,4)\,3)'
    E="0.4*sin(2*PI*(${F})*t)*sin(PI*mod(t*4\,1))"; A="aevalsrc=${E}|${E}*0.7"
    ffmpeg -f lavfi -i "${A}:s=48000" -t 4 -c:a libopus -b:a 24k arpeggio.opus
    ffmpeg -f lavfi -i "${A}:s=44100" -t 4 -c:a vorbis -strict -2 -q:a 2 arpeggio.ogg
    ffmpeg -f lavfi -i "testsrc2=size=320x180:rate=24" -f lavfi -i "${A}:s=48000" -t 2 \
      -c:v libvpx -b:v 300k -g 48 -c:a libopus -b:a 24k testsrc-320x180.webm
    ffmpeg -f lavfi -i "testsrc2=size=160x90:rate=24" -f lavfi -i "${A}:s=44100" -t 2 \
      -c:v libvpx -b:v 120k -g 48 -c:a vorbis -strict -2 -q:a 2 testsrc-160x90.webm

The three MP3 files were made for this repository on 2026-11-26 (issue
https://github.com/danbri/factoidal-core/issues/1169; record
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`), also CC0 1.0: a 4 s stereo C major
arpeggio (C4 E4 G4 C5 G4 E4 C4 G3, half a second each, sine tones at 0.45 with a 20 ms rise
and an exp(-3t) decay; the right channel a fifth above the left) written as a 16-bit WAV by a
Python script, then encoded with LAME 3.100 (Ubuntu 24.04):

    lame --quiet -b 128 arpeggio.wav arpeggio-cbr128.mp3
    lame --quiet -V 2 arpeggio.wav arpeggio-vbr.mp3
    lame --quiet -m m --resample 22.05 -b 48 arpeggio.wav arpeggio-mono22.mp3

The script, and the checks of the MP3 decoder module against minimp3 built natively and against
FFmpeg, are in `danbri/factoidal-builds`, `third_party/media-decoders/tests/` and `PROVENANCE.md`.
