#!/usr/bin/env python3
"""Deterministic Turtle inputs for the measurements (people, names, ages,
knows edges). Usage: gen-data.py <people> > out.ttl"""
import sys
n = int(sys.argv[1])
print("@prefix ex: <http://example.org/> .")
print("@prefix foaf: <http://xmlns.com/foaf/0.1/> .")
print("@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .")
for i in range(n):
    knows = ", ".join(f"ex:p{(i * 7 + k) % n}" for k in (1, 2, 3))
    print(f'ex:p{i} a foaf:Person ; foaf:name "Person {i}"@en ; '
          f'foaf:age "{20 + i % 50}"^^xsd:integer ; foaf:knows {knows} .')
