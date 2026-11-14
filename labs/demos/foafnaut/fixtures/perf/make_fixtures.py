#!/usr/bin/env python3
"""Generate the performance fixtures of Foafnaut's perf gate (skills/perf-gate/SKILL.md).

Original constructs of the size and kinds that real sites use; no text or markup is copied
from any site. The output is deterministic (own PRNG, no dependency beyond the standard
library), so the files in this directory are what this script writes, and
manifest.json states each fixture's size and the SHA-256 of every file. A change to this
script changes the fixture-set hash, which every perf record carries: rows of two
fixture sets are never compared.

    python3 labs/demos/foafnaut/fixtures/perf/make_fixtures.py          # write
    python3 labs/demos/foafnaut/fixtures/perf/make_fixtures.py --check  # verify, write nothing
    python3 labs/demos/foafnaut/fixtures/perf/make_fixtures.py --png    # write only the PNG files

The PNG files are not committed (the lab ignores *.png): the perf driver writes them with
--png, then checks the whole set with --check.

Fixtures (sizes are checked below and written to the manifest):
  article  a long article: 3,000 elements, a linked sheet of 2,000 style rules (descendant,
           class, compound, attribute and structural selectors, :hover/:focus rules,
           ::before, @media blocks, custom properties read with var())
  cards    500 cards in a grid, each a flex column with a flex row inside
  table    a table of 2,000 body cells (100 rows of 20) and a header row
  script   10 module scripts; a keyed reconcile loop over a list; 20,000 DOM calls or more,
           with layout reads (getBoundingClientRect, getComputedStyle) between rounds
  images   34 PNG images of three sizes, 6 SVG files and 4 inline SVG drawings
  form     a form of 240 controls in fieldsets, with a script that fills and validates it
  cascade  3,000 elements with short text and 2,000 rules (class, descendant and child
           combinators, :not(), :hover, :first-child, [data-x], var()): the cascade, not text
  longtext a long plain text page: 60 sections, about 45,000 words, few rules (shaping and
           line breaking)
  reads    a script that reads layout 1,000 times with no change between (one layout is
           enough) and then writes and reads 40 times (one layout each)
  domloop  a script loop of DOM calls: 2,000 elements made, attributed, appended, queried,
           restyled by class and half removed
"""
import hashlib
import json
import os
import struct
import sys
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
VERSION = 2


class Rand:
    """xorshift32: the same numbers on every Python."""
    def __init__(self, seed):
        self.s = seed & 0xFFFFFFFF or 1

    def next(self):
        s = self.s
        s ^= (s << 13) & 0xFFFFFFFF
        s ^= s >> 17
        s ^= (s << 5) & 0xFFFFFFFF
        self.s = s
        return s

    def below(self, n):
        return self.next() % n

    def pick(self, xs):
        return xs[self.below(len(xs))]


# Invented syllables: words that belong to no language and no site.
SYL = ["ka", "lo", "mi", "ren", "tas", "vo", "qui", "bel", "dor", "fen", "gu", "hal", "jot", "mur",
       "nes", "pa", "sil", "tro", "ul", "wen", "yra", "zo", "cal", "bri", "eth", "ono"]


def word(r):
    return "".join(r.pick(SYL) for _ in range(1 + r.below(3)))


def sentence(r, n):
    w = [word(r) for _ in range(n)]
    w[0] = w[0].capitalize()
    return " ".join(w) + "."


class Doc:
    """An HTML writer that counts the elements it opens."""
    VOID = {"meta", "link", "img", "input", "br", "hr", "col", "source"}

    def __init__(self):
        self.out, self.elements = [], 0

    def open(self, tag, attrs=""):
        self.elements += 1
        self.out.append(f"<{tag}{' ' + attrs if attrs else ''}>")

    def close(self, tag):
        self.out.append(f"</{tag}>")

    def el(self, tag, text="", attrs=""):
        self.open(tag, attrs)
        if tag not in self.VOID:
            self.out.append(text)
            self.close(tag)

    def raw(self, s):
        self.out.append(s)

    def html(self):
        return "".join(self.out)


def head(d, title, sheet=None, extra=""):
    d.raw("<!doctype html>\n")
    d.open("html", 'lang="en"')
    d.open("head")
    d.el("meta", attrs='charset="utf-8"')
    d.el("meta", attrs='name="viewport" content="width=device-width, initial-scale=1"')
    d.el("title", title)
    if sheet:
        d.el("link", attrs=f'rel="stylesheet" href="{sheet}"')
    d.raw(extra)
    d.close("head")


# ---- article: 3,000 elements, 2,000 rules ------------------------------------------------

ARTICLE_ELEMENTS = 3000
ARTICLE_RULES = 2000
CLASSES = [f"k{i}" for i in range(400)]          # class names the page uses
UNUSED = [f"u{i}" for i in range(900)]           # class names only the sheet knows (most real rules match nothing)


def article():
    r = Rand(0xA271C1E)
    d = Doc()
    head(d, "Article fixture", "article.css")
    d.open("body", 'class="page theme-a"')
    d.open("header", 'class="site-header"')
    d.el("a", "Brand", 'class="brand k1" href="#top"')
    d.open("nav", 'class="nav" aria-label="Sections"')
    d.open("ul", 'class="nav-list"')
    for i in range(12):
        d.open("li", f'class="nav-item {CLASSES[i]}"')
        d.el("a", word(r), f'href="#s{i}" class="nav-link"')
        d.close("li")
    d.close("ul")
    d.close("nav")
    d.close("header")
    d.open("main", 'class="layout" id="top"')
    d.open("article", 'class="article"')
    d.el("h1", sentence(r, 6), 'class="title"')
    d.el("p", f"By {word(r).capitalize()} {word(r).capitalize()}", 'class="byline"')
    s = 0
    tail_reserve = 40          # aside, footer and their contents
    while d.elements < ARTICLE_ELEMENTS - tail_reserve - 30:
        d.open("section", f'class="section {CLASSES[(s * 7) % 400]}" id="s{s}" data-kind="{r.pick(["note", "main", "aside"])}"')
        d.el("h2", sentence(r, 4), 'class="section-title"')
        for p in range(3 + r.below(3)):
            d.open("p", f'class="{r.pick(CLASSES)}{" lede" if p == 0 else ""}"')
            for _ in range(2 + r.below(3)):
                d.raw(sentence(r, 6 + r.below(10)) + " ")
                k = r.below(4)
                if k == 0:
                    d.el("a", word(r), f'href="#s{r.below(40)}" class="link {r.pick(CLASSES)}"')
                elif k == 1:
                    d.el("em", word(r))
                elif k == 2:
                    d.el("span", word(r), f'class="{r.pick(CLASSES)}"')
                else:
                    d.el("code", word(r))
                d.raw(" ")
            d.close("p")
        if s % 3 == 0:
            d.open("ul", 'class="list"')
            for _ in range(4):
                d.open("li", f'class="{r.pick(CLASSES)}"')
                d.raw(sentence(r, 5))
                d.close("li")
            d.close("ul")
        if s % 4 == 1:
            d.open("figure", 'class="figure"')
            d.el("div", "", f'class="figure-box {r.pick(CLASSES)}"')
            d.el("figcaption", sentence(r, 7))
            d.close("figure")
        if s % 5 == 2:
            d.open("blockquote", 'class="quote"')
            d.el("p", sentence(r, 12))
            d.close("blockquote")
        d.close("section")
        s += 1
    d.close("article")
    d.open("aside", 'class="sidebar"')
    d.el("h2", "Related", 'class="sidebar-title"')
    d.open("ul", 'class="related"')
    for i in range(8):
        d.open("li")
        d.el("a", sentence(r, 3), f'href="#s{i}" class="related-link"')
        d.close("li")
    d.close("ul")
    d.close("aside")
    d.close("main")
    d.open("footer", 'class="site-footer"')
    while d.elements < ARTICLE_ELEMENTS - 1:
        d.el("span", word(r), f'class="foot {r.pick(CLASSES)}"')
    d.el("small", "Original fixture text.")
    d.close("footer")
    d.close("body")
    d.close("html")
    assert d.elements == ARTICLE_ELEMENTS, d.elements
    return d.html() + "\n", {"elements": d.elements, "sections": s}


def article_css():
    r = Rand(0xC55)
    rules = []
    colors = [f"#{r.below(0xFFFFFF):06x}" for _ in range(24)]
    root = ";".join(f"--c{i}:{c}" for i, c in enumerate(colors)) + ";" + ";".join(f"--s{i}:{i * 4}px" for i in range(16))
    rules.append(f":root{{{root};--font:system-ui,sans-serif;--measure:42rem}}")
    rules.append("*,*::before,*::after{box-sizing:border-box}")
    rules.append("body{margin:0;font-family:var(--font);line-height:1.5;color:var(--c0);background:#fff}")
    rules.append(".site-header{display:flex;align-items:center;justify-content:space-between;padding:var(--s3) var(--s6);border-bottom:1px solid #ddd}")
    rules.append(".nav-list{display:flex;flex-wrap:wrap;gap:var(--s2);list-style:none;margin:0;padding:0}")
    rules.append(".layout{display:grid;grid-template-columns:minmax(0,1fr) 16rem;gap:var(--s8);max-width:72rem;margin:0 auto;padding:var(--s6)}")
    rules.append(".article{max-width:var(--measure)}")
    rules.append(".figure-box{height:120px;background:var(--c3);border-radius:6px}")
    rules.append(".sidebar{position:sticky;top:0;align-self:start}")
    rules.append(".site-footer{display:flex;flex-wrap:wrap;gap:4px;padding:var(--s6);background:#f4f4f4}")
    props = ["color:var(--c{})", "background-color:var(--c{})", "padding:var(--s{})", "margin-bottom:var(--s{})",
             "border-left:3px solid var(--c{})", "font-size:1.{}rem", "letter-spacing:0.0{}em", "text-decoration-color:var(--c{})",
             "outline-offset:{}px", "border-radius:{}px"]

    def decl():
        return ";".join(r.pick(props).format(r.below(16)) for _ in range(1 + r.below(3)))

    def cls():
        return "." + (r.pick(CLASSES) if r.below(3) == 0 else r.pick(UNUSED))

    def selector():
        k = r.below(14)
        if k == 0:
            return cls()
        if k == 1:
            return f".article .section {cls()}"
        if k == 2:
            return f"{cls()} p {r.pick(['a', 'em', 'span', 'code'])}"
        if k == 3:
            return f"main article > section{cls()} h2"
        if k == 4:
            return f"a.link{cls()}:hover"
        if k == 5:
            return f"{cls()}:focus-visible"
        if k == 6:
            return f'[data-kind="{r.pick(["note", "main", "aside", "extra"])}"] {cls()}'
        if k == 7:
            return f"{cls()}:nth-child({1 + r.below(4)}n+{r.below(3)})"
        if k == 8:
            return f"{cls()}::before"
        if k == 9:
            return f".section:not({cls()}) > p:first-child"
        if k == 10:
            return f":is(h2,h3){cls()} + p"
        if k == 11:
            return f"ul.list li{cls()} ~ li"
        if k == 12:
            return f'a[href^="#s{r.below(40)}"]{cls()}'
        return f"{cls()}, {cls()}"

    queries = ["(min-width: 600px)", "(max-width: 900px)", "(min-width: 1200px)", "(prefers-color-scheme: dark)",
               "(prefers-reduced-motion: reduce)", "print", "(orientation: portrait)", "(hover: hover)"]
    out = list(rules)
    count = len(rules)
    while count < ARTICLE_RULES:
        if r.below(5) == 0 and count + 8 <= ARTICLE_RULES:
            inner = []
            for _ in range(2 + r.below(7)):
                sel = selector()
                body = decl() + (";content:\"\\2022\"" if sel.endswith("::before") else "")
                inner.append(f"  {sel}{{{body}}}")
            out.append(f"@media {r.pick(queries)}{{\n" + "\n".join(inner) + "\n}")
            count += len(inner)
        else:
            sel = selector()
            body = decl() + (";content:\"\\2022\"" if sel.endswith("::before") else "")
            out.append(f"{sel}{{{body}}}")
            count += 1
    assert count == ARTICLE_RULES, count
    return "\n".join(out) + "\n", {"rules": count, "media_blocks": sum(1 for x in out if x.startswith("@media")),
                                   "custom_properties": 24 + 16 + 2}


# ---- cards: 500 cards in grid and flex -----------------------------------------------------

CARDS = 500


def cards():
    r = Rand(0xCA4D5)
    d = Doc()
    head(d, "Cards fixture", "cards.css")
    d.open("body")
    d.open("div", 'class="shell"')
    d.open("header", 'class="top"')
    d.el("strong", "Catalogue", 'class="logo"')
    d.open("nav", 'class="tabs"')
    for i in range(6):
        d.el("a", word(r), f'href="#t{i}" class="tab{" active" if i == 0 else ""}"')
    d.close("nav")
    d.close("header")
    d.open("aside", 'class="filters"')
    for i in range(10):
        d.open("label", 'class="filter"')
        d.el("input", attrs=f'type="checkbox" name="f{i}"')
        d.raw(" " + word(r))
        d.close("label")
    d.close("aside")
    d.open("main", 'class="grid"')
    for i in range(CARDS):
        d.open("article", f'class="card{" featured" if i % 17 == 0 else ""}"')
        d.el("div", "", f'class="thumb hue{i % 12}"')
        d.el("h3", sentence(r, 2 + r.below(3)), 'class="card-title"')
        d.el("p", sentence(r, 8 + r.below(14)), 'class="card-text"')
        d.open("div", 'class="meta"')
        for _ in range(3):
            d.el("span", word(r), 'class="tag"')
        d.close("div")
        d.open("div", 'class="actions"')
        d.el("a", "Open", f'href="#c{i}" class="button primary"')
        d.el("button", "Save", 'type="button" class="button"')
        d.close("div")
        d.close("article")
    d.close("main")
    d.close("div")
    d.close("body")
    d.close("html")
    css = """:root{--gap:16px;--radius:10px}
*{box-sizing:border-box}
body{margin:0;font:15px/1.45 system-ui,sans-serif;color:#1d1d1f}
.shell{display:grid;grid-template-columns:220px minmax(0,1fr);grid-template-rows:auto 1fr;grid-template-areas:"top top" "filters grid";min-height:100vh}
.top{grid-area:top;display:flex;align-items:center;gap:24px;padding:12px 24px;border-bottom:1px solid #e3e3e3}
.tabs{display:flex;gap:8px;flex:1}
.tab{padding:6px 12px;border-radius:999px;text-decoration:none;color:inherit}
.tab.active{background:#1d1d1f;color:#fff}
.filters{grid-area:filters;display:flex;flex-direction:column;gap:8px;padding:16px}
.grid{grid-area:grid;display:grid;grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:var(--gap);padding:var(--gap);align-content:start}
.card{display:flex;flex-direction:column;border:1px solid #e3e3e3;border-radius:var(--radius);overflow:hidden;background:#fff}
.card.featured{grid-column:span 2;flex-direction:row}
.card.featured .thumb{width:45%;aspect-ratio:auto}
.thumb{aspect-ratio:16/9;background:hsl(210 40% 80%)}
""" + "".join(f".hue{i}{{background:hsl({i * 30} 45% 78%)}}\n" for i in range(12)) + """.card-title{margin:12px 12px 4px;font-size:17px}
.card-text{margin:0 12px;flex:1;color:#555}
.meta{display:flex;flex-wrap:wrap;gap:6px;padding:8px 12px}
.tag{font-size:12px;padding:2px 8px;border-radius:999px;background:#f0f0f3}
.actions{display:flex;justify-content:space-between;align-items:center;gap:8px;padding:8px 12px 12px;margin-top:auto}
.button{flex:1;text-align:center;padding:6px 10px;border:1px solid #c9c9cf;border-radius:8px;background:#fff;font:inherit;text-decoration:none;color:inherit}
.button.primary{background:#0a63d8;border-color:#0a63d8;color:#fff}
.card:hover{box-shadow:0 2px 8px rgb(0 0 0/.12)}
@media (max-width:700px){.shell{grid-template-columns:1fr;grid-template-areas:"top" "grid"}.filters{display:none}.card.featured{grid-column:auto;flex-direction:column}}
"""
    return d.html() + "\n", css, {"elements": d.elements, "cards": CARDS}


# ---- table: 2,000 cells ------------------------------------------------------------------

ROWS, COLS = 100, 20


def table():
    r = Rand(0x7AB1E)
    d = Doc()
    head(d, "Table fixture", "table.css")
    d.open("body")
    d.el("h1", "Quarterly figures (invented)")
    d.open("table", 'class="data"')
    d.el("caption", "One hundred rows of twenty invented values")
    d.open("thead")
    d.open("tr")
    for c in range(COLS):
        d.el("th", f"{word(r)} {c}", 'scope="col"')
    d.close("tr")
    d.close("thead")
    d.open("tbody")
    cells = 0
    for row in range(ROWS):
        d.open("tr", f'class="{"flag" if row % 9 == 4 else ""}"' if row % 9 == 4 else "")
        for c in range(COLS):
            if c == 0:
                d.el("th", f"{word(r)}-{row}", 'scope="row"')
            else:
                v = r.below(2000000) / 100 - 5000
                d.el("td", f"{v:,.2f}", 'class="num neg"' if v < 0 else 'class="num"')
            cells += 1
        d.close("tr")
    d.close("tbody")
    d.close("table")
    d.close("body")
    d.close("html")
    assert cells == ROWS * COLS
    css = """body{margin:24px;font:14px/1.4 system-ui,sans-serif}
table.data{border-collapse:collapse;width:100%;table-layout:auto}
caption{caption-side:top;text-align:left;font-weight:600;padding:8px 0}
th,td{border:1px solid #d6d6d6;padding:4px 8px}
thead th{position:sticky;top:0;background:#f3f4f6;text-align:left}
tbody tr:nth-child(2n){background:#fafafa}
tbody tr:hover{background:#eef4ff}
tbody tr.flag{background:#fff6e5}
td.num{text-align:right;font-variant-numeric:tabular-nums}
td.neg{color:#b00020}
tbody th{font-weight:500;text-align:left;white-space:nowrap}
@media (max-width:800px){th,td{padding:2px 4px;font-size:12px}}
"""
    return d.html() + "\n", css, {"elements": d.elements, "cells": cells, "rows": ROWS, "cols": COLS}


# ---- script: 10 modules, a reconcile loop, 20,000+ DOM calls -----------------------------

MODULES = 10
ITEMS = 400
ROUNDS = 24


def script():
    d = Doc()
    head(d, "Script fixture", "script.css")
    d.open("body")
    d.open("header", 'class="bar"')
    d.el("h1", "Board")
    d.el("output", "0", 'id="count"')
    d.close("header")
    d.el("ul", "", 'id="list" class="list"')
    d.el("div", "", 'id="status"')
    # A classic script first: the host starts a page's scripts when the engine's inspection
    # lists one, and the inspection does not list module scripts (a page with only module
    # scripts runs none in the native host).
    d.el("script", "window.perfFixture = 'script';")
    d.el("script", "", 'type="module" src="script/main.js"')
    d.close("body")
    d.close("html")
    mods = {}
    # m1..m8: small library modules (state, random, keys, view, diff, dom counting, layout reads, scheduling)
    mods["rand.js"] = """// xorshift32, the same sequence in every engine
export function rand(seed) {
  let s = seed >>> 0 || 1;
  return () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s; };
}
"""
    mods["count.js"] = """// Every DOM call of the fixture goes through these, so the number of calls is known.
export const calls = { n: 0 };
export const create = (tag) => { calls.n++; return document.createElement(tag); };
export const text = (el, t) => { calls.n++; el.textContent = t; };
export const attr = (el, k, v) => { calls.n++; el.setAttribute(k, v); };
export const add = (parent, child, before) => { calls.n++; return before ? parent.insertBefore(child, before) : parent.appendChild(child); };
export const remove = (el) => { calls.n++; el.remove(); };
export const cls = (el, c, on) => { calls.n++; el.classList.toggle(c, on); };
export const query = (root, sel) => { calls.n++; return root.querySelector(sel); };
"""
    mods["state.js"] = f"""import {{ rand }} from "./rand.js";
// The items: id, title, score, done. Each round changes some, drops some, adds some and reorders.
const next = rand(0x5C121);
let serial = 0;
const words = ["ka", "lo", "mi", "ren", "tas", "vo", "qui", "bel", "dor", "fen"];
const title = () => words[next() % 10] + words[next() % 10] + " " + words[next() % 10];
export function initial() {{
  const items = [];
  for (let i = 0; i < {ITEMS}; i++) items.push({{ id: serial++, title: title(), score: next() % 1000, done: false }});
  return items;
}}
export function step(items) {{
  const out = [];
  for (const it of items) {{
    const k = next() % 20;
    if (k === 0) continue;                                       // dropped
    if (k < 5) out.push({{ ...it, score: next() % 1000 }});      // changed score
    else if (k === 5) out.push({{ ...it, done: !it.done }});      // toggled
    else if (k === 6) out.push({{ ...it, title: title() }});     // retitled
    else out.push(it);
  }}
  for (let i = 0; i < 15; i++) out.splice(next() % (out.length + 1), 0, {{ id: serial++, title: title(), score: next() % 1000, done: false }});
  if (next() % 2) out.sort((a, b) => b.score - a.score || a.id - b.id);
  return out;
}}
"""
    mods["view.js"] = """import { create, text, attr, add, cls } from "./count.js";
// One row: li > span.title + span.score + button
export function row(it) {
  const li = create("li"); attr(li, "data-id", String(it.id)); cls(li, "row", true); cls(li, "done", it.done);
  const t = create("span"); cls(t, "title", true); text(t, it.title); add(li, t);
  const s = create("span"); cls(s, "score", true); text(s, String(it.score)); add(li, s);
  const b = create("button"); attr(b, "type", "button"); text(b, it.done ? "Undo" : "Done"); add(li, b);
  return li;
}
export function update(li, old, it) {
  if (old.title !== it.title) text(li.children[0], it.title);
  if (old.score !== it.score) text(li.children[1], String(it.score));
  if (old.done !== it.done) { cls(li, "done", it.done); text(li.children[2], it.done ? "Undo" : "Done"); }
}
"""
    mods["diff.js"] = """import { add, remove } from "./count.js";
import { row, update } from "./view.js";
// A keyed reconcile, as list libraries do: keep, update, move, insert and remove by id.
export function reconcile(parent, nodes, olds, items) {
  const next = new Map();
  const byId = new Map(olds.map((o) => [o.id, o]));
  const wanted = new Set(items.map((i) => i.id));
  for (const [id, li] of nodes) if (!wanted.has(id)) remove(li);
  let cursor = parent.firstElementChild;
  for (const it of items) {
    let li = nodes.get(it.id);
    if (li) { update(li, byId.get(it.id), it); if (li !== cursor) add(parent, li, cursor); else cursor = cursor.nextElementSibling; }
    else { li = row(it); add(parent, li, cursor); }
    next.set(it.id, li);
  }
  return next;
}
"""
    mods["measure.js"] = """import { query, calls } from "./count.js";
// Layout reads between rounds, as pages do to place things: each forces style and layout.
export function measure(list) {
  let h = 0;
  for (let k = 1; k <= 4; k++) {
    const li = query(list, `li:nth-child(${k * 7})`);
    if (li) { calls.n++; h += li.getBoundingClientRect().height; calls.n++; h += getComputedStyle(li).color.length; }
  }
  return h;
}
"""
    mods["schedule.js"] = """// Rounds after the first run as tasks, so the page settles over several turns.
export function later(f) { setTimeout(f, 0); }
"""
    mods["status.js"] = """import { text, query } from "./count.js";
export function status(n, round) { text(query(document, "#count"), String(n)); text(query(document, "#status"), "round " + round); }
"""
    mods["format.js"] = """export const plural = (n, w) => n + " " + w + (n === 1 ? "" : "s");
export const pad = (s, n) => (s + " ".repeat(n)).slice(0, n);
"""
    mods["main.js"] = f"""import {{ initial, step }} from "./state.js";
import {{ reconcile }} from "./diff.js";
import {{ measure }} from "./measure.js";
import {{ later }} from "./schedule.js";
import {{ status }} from "./status.js";
import {{ plural }} from "./format.js";
import {{ calls }} from "./count.js";
const list = document.getElementById("list");
let items = initial(), nodes = reconcile(list, new Map(), [], items), round = 0, read = 0;
read += measure(list);
function tick() {{
  const next = step(items);
  nodes = reconcile(list, nodes, items, next);
  items = next;
  read += measure(list);
  status(items.length, ++round);
  if (round < {ROUNDS}) later(tick);
  else console.log("perf-fixture-done " + JSON.stringify({{ domCalls: calls.n, items: items.length, rounds: round, read: read > 0, label: plural(round, "round") }}));
}}
later(tick);
"""
    assert len(mods) == MODULES
    css = """body{margin:0;font:14px/1.4 system-ui,sans-serif}
.bar{display:flex;justify-content:space-between;align-items:center;padding:8px 16px;background:#20232a;color:#fff}
.list{list-style:none;margin:0;padding:0 16px}
.row{display:grid;grid-template-columns:1fr 5rem 5rem;align-items:center;gap:8px;padding:4px 0;border-bottom:1px solid #eee}
.row.done .title{text-decoration:line-through;color:#888}
.score{text-align:right;font-variant-numeric:tabular-nums}
.row:nth-child(2n){background:#fafafa}
"""
    return d.html() + "\n", css, mods, {"elements": d.elements, "modules": MODULES, "items": ITEMS, "rounds": ROUNDS,
                                         "dom_calls_at_least": 20000}


# ---- images ------------------------------------------------------------------------------

def png(width, height, seed):
    """A gradient with bands: deflate keeps the file small, the decoder still sees every pixel."""
    r = Rand(seed)
    a, b = [r.below(256) for _ in range(3)], [r.below(256) for _ in range(3)]
    rows = []
    for y in range(height):
        band = (y // 16) % 2
        line = bytearray([0])
        for x in range(width):
            t = x * 255 // max(1, width - 1)
            for c in range(3):
                v = (a[c] * (255 - t) + b[c] * t) // 255
                line.append(v ^ (32 if band else 0))
        rows.append(bytes(line))
    raw = b"".join(rows)

    def chunk(kind, data):
        return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data) & 0xFFFFFFFF)
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)) +
            chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b""))


def svg(seed, w=320, h=200):
    r = Rand(seed)
    shapes = []
    for i in range(24):
        x, y = r.below(w), r.below(h)
        if i % 3 == 0:
            shapes.append(f'<circle cx="{x}" cy="{y}" r="{4 + r.below(30)}" fill="hsl({r.below(360)} 60% 60%)"/>')
        elif i % 3 == 1:
            shapes.append(f'<rect x="{x}" y="{y}" width="{8 + r.below(60)}" height="{8 + r.below(40)}" rx="4" fill="hsl({r.below(360)} 50% 70%)"/>')
        else:
            pts = " ".join(f"{r.below(w)},{r.below(h)}" for _ in range(4))
            shapes.append(f'<path d="M{pts.replace(" ", " L")} Z" fill="none" stroke="hsl({r.below(360)} 40% 40%)" stroke-width="2"/>')
    return f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {w} {h}" width="{w}" height="{h}">' + "".join(shapes) + "</svg>"


IMAGE_SET = [(256, 160)] * 24 + [(640, 400)] * 8 + [(1280, 800)] * 2


def images():
    r = Rand(0x1A6E5)
    files = {}
    d = Doc()
    head(d, "Images fixture", "images.css")
    d.open("body")
    d.el("h1", "Gallery (generated pictures)")
    d.open("div", 'class="hero"')
    for i, (w, h) in enumerate(IMAGE_SET):
        name = f"images/p{i:02d}.png"
        files[name] = png(w, h, 0x900 + i)
        if (w, h) == (1280, 800):
            d.el("img", attrs=f'src="{name}" width="{w // 2}" height="{h // 2}" alt="{word(r)}" class="wide"')
    d.close("div")
    d.open("div", 'class="gallery"')
    for i, (w, h) in enumerate(IMAGE_SET):
        if (w, h) == (1280, 800):
            continue
        d.open("figure")
        d.el("img", attrs=f'src="images/p{i:02d}.png" width="{w}" height="{h}" alt="{word(r)}"' + (' loading="lazy"' if i > 20 else ""))
        d.el("figcaption", sentence(r, 4))
        d.close("figure")
    for i in range(6):
        name = f"images/s{i}.svg"
        files[name] = svg(0x5000 + i).encode()
        d.open("figure")
        d.el("img", attrs=f'src="{name}" width="320" height="200" alt="{word(r)}"')
        d.el("figcaption", sentence(r, 4))
        d.close("figure")
    for i in range(4):
        d.open("figure")
        d.raw(svg(0x6000 + i, 240, 150))
        d.el("figcaption", sentence(r, 4))
        d.close("figure")
    d.close("div")
    d.close("body")
    d.close("html")
    css = """body{margin:0;font:14px/1.4 system-ui,sans-serif}
h1{margin:16px}
.hero{display:flex;gap:8px;padding:0 16px}
.hero img{flex:1;min-width:0;height:auto}
.gallery{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:12px;padding:16px}
figure{margin:0}
figure img,figure svg{display:block;width:100%;height:auto;border-radius:6px}
figcaption{font-size:12px;color:#555;padding-top:4px}
"""
    pixels = sum(w * h for w, h in IMAGE_SET)
    return d.html() + "\n", css, files, {"elements": d.elements, "png": len(IMAGE_SET), "png_pixels": pixels, "svg_files": 6, "inline_svg": 4}


# ---- form ----------------------------------------------------------------------------------

FIELDSETS, PER_SET = 12, 20


def form():
    r = Rand(0xF0F0)
    d = Doc()
    head(d, "Form fixture", "form.css")
    d.open("body")
    d.open("form", 'id="f" class="form" novalidate')
    d.el("h1", "Application (invented)")
    kinds = ["text", "email", "number", "date", "checkbox", "radio", "range", "color", "tel", "url", "select", "textarea", "password", "search"]
    controls = 0
    for fs in range(FIELDSETS):
        d.open("fieldset", 'class="group"')
        d.el("legend", sentence(r, 3))
        for i in range(PER_SET):
            k = kinds[(fs * PER_SET + i) % len(kinds)]
            name = f"f{fs}_{i}"
            d.open("div", 'class="row"')
            d.el("label", word(r).capitalize(), f'for="{name}"')
            if k == "select":
                d.open("select", f'id="{name}" name="{name}"')
                for o in range(10):
                    d.el("option", word(r), f'value="{o}"')
                d.close("select")
            elif k == "textarea":
                d.el("textarea", "", f'id="{name}" name="{name}" rows="3" maxlength="400"')
            else:
                extra = {"number": ' min="0" max="100"', "text": ' required minlength="2"', "email": " required",
                         "tel": ' pattern="[0-9 ]{6,}"', "range": ' min="0" max="10"', "radio": f' value="{i}"'}.get(k, "")
                d.el("input", attrs=f'type="{k}" id="{name}" name="{name if k != "radio" else f"r{fs}"}"{extra}')
            d.el("small", sentence(r, 5), 'class="hint"')
            d.close("div")
            controls += 1
        d.close("fieldset")
    d.open("div", 'class="actions"')
    d.el("button", "Submit", 'type="submit"')
    d.el("button", "Reset", 'type="reset"')
    d.close("div")
    d.close("form")
    d.el("script", """
const f = document.getElementById("f");
let set = 0, invalid = 0;
for (const el of f.elements) {
  if (el.type === "text" || el.type === "search") { el.value = "value " + set; set++; }
  else if (el.type === "number") { el.value = String(set % 140); set++; }
  else if (el.type === "checkbox") { el.checked = set % 2 === 0; set++; }
  else if (el.tagName === "SELECT") { el.selectedIndex = set % 10; set++; }
}
for (const el of f.elements) if (el.willValidate && !el.checkValidity()) invalid++;
console.log("perf-fixture-done " + JSON.stringify({ set, invalid, valid: f.checkValidity() }));
""")
    d.close("body")
    d.close("html")
    css = """body{margin:0;font:15px/1.4 system-ui,sans-serif;background:#f6f7f9}
.form{max-width:860px;margin:24px auto;padding:24px;background:#fff;border-radius:12px}
.group{border:1px solid #dfe1e5;border-radius:8px;margin:0 0 16px;padding:12px 16px;display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px 20px}
legend{font-weight:600;padding:0 4px}
.row{display:flex;flex-direction:column;gap:2px}
label{font-size:13px;color:#333}
input,select,textarea{font:inherit;padding:6px 8px;border:1px solid #c4c7cc;border-radius:6px}
input[type=checkbox],input[type=radio]{align-self:flex-start}
input:invalid,textarea:invalid{border-color:#c62828}
input:focus-visible,select:focus-visible{outline:2px solid #1a73e8}
.hint{color:#6b6f76;font-size:12px}
.actions{display:flex;gap:12px;justify-content:flex-end}
@media (max-width:700px){.group{grid-template-columns:1fr}}
"""
    return d.html() + "\n", css, {"elements": d.elements, "controls": controls, "fieldsets": FIELDSETS}


# ---- cascade: 2,000 rules over 3,000 elements of short text ---------------------------------

CASCADE_ELEMENTS, CASCADE_RULES = 3000, 2000


def cascade():
    r = Rand(0xCA5CADE)
    d = Doc()
    head(d, "Cascade fixture", "cascade.css")
    d.open("body", 'class="app"')
    d.open("div", 'class="root" data-x="0"')
    g = 0
    while d.elements < CASCADE_ELEMENTS - 12:
        d.open("section", f'class="group c{g % 50}" data-x="{g % 7}"')
        d.el("h3", word(r), f'class="head c{r.below(50)}"')
        d.open("ul", f'class="items c{r.below(50)}"')
        for i in range(6):
            d.open("li", f'class="item c{r.below(50)} {"odd" if i % 2 else "even"}" data-x="{r.below(9)}"')
            d.el("span", word(r), f'class="label c{r.below(50)}"')
            d.el("a", word(r), f'href="#g{g}" class="link c{r.below(50)}"')
            d.close("li")
        d.close("ul")
        d.close("section")
        g += 1
    d.close("div")
    while d.elements < CASCADE_ELEMENTS:
        d.el("p", word(r), 'class="tail"')
    d.close("body")
    d.close("html")
    assert d.elements == CASCADE_ELEMENTS, d.elements
    r = Rand(0x5E1EC7)
    rules = [":root{" + ";".join(f"--v{i}:{i * 3}px" for i in range(20)) + "}",
             "body{margin:0;font:14px/1.4 sans-serif}", ".group{padding:4px;margin:2px 0}"]
    tags = ["section", "ul", "li", "span", "a", "h3", "div"]

    def c():
        return f".c{r.below(80)}"            # c50..c79 match nothing, as most rules of a site

    def sel():
        k = r.below(10)
        return [lambda: f"{c()} {r.pick(tags)}",
                lambda: f"{r.pick(tags)}{c()} > {r.pick(tags)}",
                lambda: f"{c()}:not({c()}) {r.pick(['span', 'a'])}",
                lambda: f"{r.pick(['li', 'a'])}{c()}:hover",
                lambda: f"{c()} li:first-child",
                lambda: f'[data-x="{r.below(9)}"] {c()}',
                lambda: f".root .group {c()}",
                lambda: f"{c()}.{r.pick(['odd', 'even'])} > .label",
                lambda: f"section{c()} ~ section {c()}",
                lambda: f"{c()}"][k]()
    while len(rules) < CASCADE_RULES:
        rules.append(f"{sel()}{{padding-left:var(--v{r.below(20)});color:#{r.below(0xFFFFFF):06x}}}")
    return d.html() + "\n", "\n".join(rules) + "\n", {"elements": d.elements, "rules": len(rules), "groups": g}


# ---- longtext: about 45,000 words --------------------------------------------------------------

LONG_SECTIONS = 60


def longtext():
    r = Rand(0x1047E47)
    d = Doc()
    head(d, "Long text fixture", "longtext.css")
    d.open("body")
    d.open("main", 'class="text"')
    d.el("h1", sentence(r, 5))
    words = 0
    for s in range(LONG_SECTIONS):
        d.el("h2", sentence(r, 4))
        for _ in range(6):
            d.open("p")
            for _ in range(8):
                n = 10 + r.below(10)
                words += n
                d.raw(sentence(r, n) + " ")
                if r.below(6) == 0:
                    d.el("em", word(r))
                    d.raw(" ")
            d.close("p")
    d.close("main")
    d.close("body")
    d.close("html")
    css = """body{margin:0;font:16px/1.6 sans-serif;color:#222}
.text{max-width:46rem;margin:0 auto;padding:24px}
h2{margin:2em 0 .5em}
p{margin:0 0 1em;text-align:left;hyphens:manual}
"""
    return d.html() + "\n", css, {"elements": d.elements, "sections": LONG_SECTIONS, "words": words}


# ---- reads: layout reads with and without writes between ---------------------------------------

READS_CLEAN, READS_DIRTY = 1000, 40


def reads():
    r = Rand(0x4EAD5)
    d = Doc()
    head(d, "Layout reads fixture", "reads.css")
    d.open("body")
    d.open("div", 'id="box" class="box"')
    for i in range(300):
        d.el("div", sentence(r, 3 + r.below(6)), f'class="cell" id="e{i}"')
    d.close("div")
    d.el("script", f"""
const cells = Array.from(document.querySelectorAll(".cell"));
let sum = 0, reads = 0;
// Reads with nothing changed between: the first lays out the page, the rest reuse it.
for (let i = 0; i < {READS_CLEAN}; i++) {{ const el = cells[i % cells.length]; sum += el.offsetHeight + el.getBoundingClientRect().width; reads += 2; }}
// A write, then a read: each read lays out again (at most).
for (let i = 0; i < {READS_DIRTY}; i++) {{ const el = cells[(i * 7) % cells.length]; el.style.width = (200 + (i % 50) * 4) + "px"; sum += el.offsetHeight; reads++; }}
console.log("perf-fixture-done " + JSON.stringify({{ reads, sum: sum > 0 }}));
""")
    d.close("body")
    d.close("html")
    css = """body{margin:0;font:14px/1.4 sans-serif}
.box{display:flex;flex-wrap:wrap;gap:4px;padding:8px}
.cell{width:240px;padding:4px;border:1px solid #ccc}
"""
    return d.html() + "\n", css, {"elements": d.elements, "reads_clean": READS_CLEAN, "reads_dirty": READS_DIRTY}


# ---- domloop: a script loop of DOM calls -----------------------------------------------------

DOMLOOP_N = 2000


def domloop():
    d = Doc()
    head(d, "DOM loop fixture", "domloop.css")
    d.open("body")
    d.el("div", "", 'id="root"')
    d.el("script", f"""
const root = document.getElementById("root");
let calls = 0;
const frag = document.createDocumentFragment();
for (let i = 0; i < {DOMLOOP_N}; i++) {{
  const el = document.createElement(i % 3 ? "span" : "div");
  el.className = "n k" + (i % 10);
  el.setAttribute("data-i", String(i));
  el.textContent = "item " + i;
  frag.appendChild(el);
  calls += 5;
}}
root.appendChild(frag); calls++;
const hits = root.querySelectorAll(".k3, .k7"); calls++;
for (const el of hits) {{ el.classList.add("hit"); calls++; }}
let len = 0;
for (let el = root.firstElementChild; el; el = el.nextElementSibling) {{ len += el.getAttribute("data-i").length; calls += 2; }}
const all = root.children;
for (let i = all.length - 1; i >= 0; i -= 2) {{ all[i].remove(); calls++; }}
console.log("perf-fixture-done " + JSON.stringify({{ domCalls: calls, left: root.children.length, len }}));
""")
    d.close("body")
    d.close("html")
    css = """body{margin:0;font:13px/1.3 sans-serif}
#root{display:flex;flex-wrap:wrap;gap:2px;padding:8px}
.n{padding:1px 3px;border:1px solid #ddd}
.hit{background:#ffe9a8}
"""
    return d.html() + "\n", css, {"elements": d.elements, "nodes": DOMLOOP_N, "dom_calls_at_least": 10000}


# ---- write / check -------------------------------------------------------------------------

def build():
    files, fixtures = {}, {}
    html, a_meta = article()
    css, c_meta = article_css()
    files["article.html"], files["article.css"] = html.encode(), css.encode()
    fixtures["article"] = {"page": "article.html", "scripted": False, **a_meta, **c_meta}
    html, css, meta = cards()
    files["cards.html"], files["cards.css"] = html.encode(), css.encode()
    fixtures["cards"] = {"page": "cards.html", "scripted": False, **meta}
    html, css, meta = table()
    files["table.html"], files["table.css"] = html.encode(), css.encode()
    fixtures["table"] = {"page": "table.html", "scripted": False, **meta}
    html, css, mods, meta = script()
    files["script.html"], files["script.css"] = html.encode(), css.encode()
    for k, v in mods.items():
        files["script/" + k] = v.encode()
    fixtures["script"] = {"page": "script.html", "scripted": True, **meta}
    html, css, imgs, meta = images()
    files["images.html"], files["images.css"] = html.encode(), css.encode()
    files.update(imgs)
    fixtures["images"] = {"page": "images.html", "scripted": False, **meta}
    html, css, meta = form()
    files["form.html"], files["form.css"] = html.encode(), css.encode()
    fixtures["form"] = {"page": "form.html", "scripted": True, **meta}
    html, css, meta = cascade()
    files["cascade.html"], files["cascade.css"] = html.encode(), css.encode()
    fixtures["cascade"] = {"page": "cascade.html", "scripted": False, **meta}
    html, css, meta = longtext()
    files["longtext.html"], files["longtext.css"] = html.encode(), css.encode()
    fixtures["longtext"] = {"page": "longtext.html", "scripted": False, **meta}
    html, css, meta = reads()
    files["reads.html"], files["reads.css"] = html.encode(), css.encode()
    fixtures["reads"] = {"page": "reads.html", "scripted": True, **meta}
    html, css, meta = domloop()
    files["domloop.html"], files["domloop.css"] = html.encode(), css.encode()
    fixtures["domloop"] = {"page": "domloop.html", "scripted": True, **meta}
    hashes = {k: hashlib.sha256(v).hexdigest() for k, v in sorted(files.items())}
    for name, fx in fixtures.items():
        stem = fx["page"].rsplit(".", 1)[0]
        own = [k for k in hashes if k.split("/")[0].split(".")[0] == stem]
        fx["files"] = len(own)
        fx["bytes"] = sum(len(files[k]) for k in own)
    set_hash = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    manifest = {"version": VERSION, "generator": "make_fixtures.py", "set_sha256": set_hash, "viewport": [1280, 800],
                "fixtures": fixtures, "files": hashes}
    files["manifest.json"] = (json.dumps(manifest, indent=1, sort_keys=True) + "\n").encode()
    return files, manifest


def main():
    check = "--check" in sys.argv
    files, manifest = build()
    if "--png" in sys.argv:
        files = {k: v for k, v in files.items() if k.endswith(".png")}
    bad = []
    for rel, data in files.items():
        path = os.path.join(HERE, rel)
        if check:
            try:
                if open(path, "rb").read() != data:
                    bad.append(rel)
            except OSError:
                bad.append(rel)
        else:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "wb") as f:
                f.write(data)
    if check and bad:
        print("stale or missing:", ", ".join(bad[:10]), file=sys.stderr)
        sys.exit(1)
    for name, fx in manifest["fixtures"].items():
        print(f"{name:8} {fx['bytes']:>9,} bytes  {fx['elements']:>5} elements  " +
              ", ".join(f"{k} {v}" for k, v in fx.items() if k not in ("page", "bytes", "elements", "files", "scripted")))
    print("set", manifest["set_sha256"][:16])


if __name__ == "__main__":
    main()
