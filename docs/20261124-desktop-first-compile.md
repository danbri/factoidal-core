# 2026-11-24 — Compile desktop pages once before first presentation

The desktop host compiled a full 1280×800 document before opening the window. Its
artifact was never drawn. The first presented frame then compiled the document
again, with the actual backing extent, chrome and scroll band.

The normal render loop now supplies the first frame and its hit geometry. Input
before the first frame still goes through the existing queue. The CPU-only
engine check still requests a standalone artifact and checks its render plan.

The archived BBC News desktop replay (factoidal-builds run 45466307369) measured
10.46 and 13.77 seconds in the first presented frame's scripts-on layout. The
trace also showed an earlier `native-html-loaded` event from the unused compile.
The paired check pins the native engine, host dependencies and captures while
alternating this host change. First-paint savings and visual parity are measured
separately.
