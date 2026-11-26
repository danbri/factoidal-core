#!/usr/bin/env python3
"""Compare a page's text in Foafnaut (Textnaut --dump) with Chrome's (document.body.innerText):
the words of 4 or more letters in each, and the share of Chrome's words that Textnaut shows.
Line breaks after a hyphen are joined first; Textnaut's link list and [n] markers are left out.

Usage: tools/hub-text-compare.py CHROME.txt TEXTNAUT.txt
Record of use: docs/designissues/2026-11-26-hub-pages-in-foafnaut.md section 3
(https://github.com/danbri/factoidal-core/issues/1161)."""
import re, sys

def words(text):
    text = re.sub(r"-\n", "-", text)
    text = re.sub(r"\[\d+\]", " ", text)
    return set(re.findall(r"[A-Za-z][A-Za-z0-9]{3,}", text))

chrome, tn = open(sys.argv[1]).read(), open(sys.argv[2]).read()
if "\nLinks:\n" in tn:
    tn = tn.split("\nLinks:\n")[0]
a, b = words(chrome), words(tn)
print(f"chrome {len(a)} words, textnaut {len(b)}; of Chrome's words, textnaut shows {len(a & b)} "
      f"({100 * len(a & b) / max(1, len(a)):.1f}%)")
print("missing:", " ".join(sorted(a - b)[:50]), flush=True)
print("extra:", " ".join(sorted(b - a)[:30]))
