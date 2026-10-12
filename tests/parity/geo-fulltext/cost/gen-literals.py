#!/usr/bin/env python3
"""Write a Turtle file with N subjects, each with one rdfs:label literal of
3 to 8 words drawn from a 404-word vocabulary (seed 727, so the file is the
same on every run). The fixture of the text:query cost measurement in
docs/designissues/2026-10-10-lean-geo-distance-fulltext.md, section 4.

Usage: python3 gen-literals.py 10000 > ft10k.ttl
"""
import random, sys
n = int(sys.argv[1])
rng = random.Random(727)
vocab = [f"w{i:03d}" for i in range(400)] + ["panel", "solar", "heater", "storage"]
print("@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .")
print("@prefix ex: <http://example.org/> .")
for i in range(n):
    words = [rng.choice(vocab) for _ in range(rng.randint(3, 8))]
    print(f'ex:s{i} rdfs:label "{" ".join(words).capitalize()}" .')
