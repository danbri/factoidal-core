# 2026-11-25 Reuse a pinned HTTPS connection for a page's fonts

Font transfer still uses the address and redirect decisions made by Lean.
The serial font load can reuse its HTTPS transport when the authority,
port and approved address match. The scope ends when the font loop exits.
The selected faces, source fallback order, byte limits and fonts handed to
the renderer are the same.

On a native Linux browser comparison, BBC News received the same 20 fonts
and rendered identical pixels. The font transfers took 2.15 and 2.10
seconds before reuse and 0.44 and 0.49 seconds with reuse. GOV.UK's two fonts
showed no clear change. Those four processes also rendered matching pixels.

[Browser comparison](https://github.com/danbri/factoidal-builds/actions/runs/45540812352)
