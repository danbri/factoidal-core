---
title: "Notebook: cells drawn by the built-in engine"
description: "Hub cells whose output is laid out and drawn by the built-in browser engine: a page drawn into a canvas, a Foafnaut view with scripts, and Textnaut's text grid, from one engine, with each cell's timings."
layout: hub.njk
tests: tests/hub/hub_notebook_test.mjs
---

# Notebook: cells drawn by the built-in engine

<p class="warning"><strong>⚠️ EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE.</strong></p>

[Hub](../) · [Foafnaut](../foafnaut/) · [Textnaut](../textnaut/)

The cells on this page give their output to the built-in engine, the one that draws
the [Foafnaut](../foafnaut/) browser. One engine serves the whole page: it starts in
a worker when the first cell asks for it, and every cell after that uses the same
one. The library cell at the end, `nb`, has three ways to show a page:

- `nb.render(htmlOrSvg)`: the engine lays the markup out and draws it into a canvas
  in the cell. No browser around it and no scripts.
- `nb.foafnaut(urlOrHtml)`: a Foafnaut view. The page's scripts run on BubblePopJS,
  the built-in JavaScript engine; a click goes to the page, and a link is followed
  inside the cell. Back returns to the page before.
- `nb.textnaut(urlOrHtml)`: the same layout as text, the way the terminal program
  Textnaut shows it, with a number beside each link. Click a link, or focus the grid
  and type its number and Enter.

Under each output is what that cell cost: the engine's start (first cell only),
preparing the page, its scripts, layout, drawing (on the GPU, or on the CPU by the
engine when this browser has no WebGPU), the text cells, and how many primitives,
glyph runs and links the engine made. A URL must be a page of this site: the Hub
does not fetch other sites.

## A page drawn by the engine

A small page as a string. Edit it and press Run: the cells that use it draw again.

```observable-js
card = `<style>
  body{font-family:sans-serif;margin:12px;color:#223}
  .card{border:2px solid #4a7;border-radius:8px;padding:10px 14px;background:#f3fbf6}
  h2{margin:0 0 6px;color:#275}
  .tag{display:inline-block;background:#275;color:#fff;border-radius:4px;padding:0 6px;font-size:12px}
</style>
<div class="card">
  <h2>Notebook card</h2>
  <p>Laid out and drawn by the <b>built-in engine</b>, not by this browser.
  <span class="tag">BubblePopKit</span></p>
  <ul><li>Block and inline layout</li><li>Borders, colours and rounded corners</li>
  <li>A link to <a href="../foafnaut/pages/index.html">the demo pages</a></li></ul>
</div>`
```

```observable-js
nb.render(card)
```

## SVG from data

The markup can come from a computation. Here a cell makes a bar chart as SVG from an
array, and the engine draws it.

```observable-js
bars = [["Mon", 12], ["Tue", 19], ["Wed", 7], ["Thu", 15], ["Fri", 23]]
```

```observable-js
nb.render(`<svg xmlns="http://www.w3.org/2000/svg" width="360" height="180" viewBox="0 0 360 180">
  <rect width="360" height="180" fill="#fbfbf8"/>
  ${bars.map(([day, n], i) => `<rect x="${20 + i * 66}" y="${160 - n * 6}" width="44" height="${n * 6}" rx="4" fill="hsl(${150 + i * 30} 55% 45%)"/>
  <text x="${42 + i * 66}" y="176" font-size="12" text-anchor="middle" fill="#333">${day}</text>
  <text x="${42 + i * 66}" y="${154 - n * 6}" font-size="12" text-anchor="middle" fill="#333">${n}</text>`).join("")}
</svg>`, { width: 380 })
```

## The same input both ways

The card again, drawn on the left and as Textnaut's text on the right.

```observable-js
nb.sideBySide(card)
```

## A Foafnaut view with a script

This page has a script. BubblePopJS runs it before the first frame (the counter says
0 clicks, not "no script"), and a click on "Count" goes to the page's own click
handler. "Demo pages" is a link of this site: it opens inside the cell.

```observable-js
counter = `<style>body{font-family:sans-serif;margin:12px}#n{font-size:28px;color:#264}a{margin-right:12px}</style>
<p id="n">no script</p>
<p><a href="#" id="count">Count</a> <a href="../foafnaut/pages/index.html">Demo pages</a></p>
<script>
  let clicks = 0;
  const n = document.getElementById("n");
  n.textContent = "0 clicks";
  document.getElementById("count").addEventListener("click", (event) => {
    event.preventDefault();
    clicks++;
    n.textContent = clicks + (clicks === 1 ? " click" : " clicks");
  });
</script>`
```

```observable-js
nb.foafnaut(counter, { height: 220 })
```

## A page of this site as text

The demo index of the Foafnaut browser, as Textnaut shows it. The links are
numbered; following one opens that page as text in this cell.

```observable-js
nb.textnaut("../foafnaut/pages/index.html", { cols: 80 })
```

## What each cell cost

Every cell above, as it finished.

```observable-js
nb.timingTable()
```

## The library

```observable-js closed title="Library: the engine's cell outputs (nb)"
nb = import(new URL("../notebook/cells.mjs", location.href).href)
```
