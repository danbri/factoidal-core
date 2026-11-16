---
title: Web platform
description: The Hub pages about Foafnaut, the web browser with its own built-in engine, and Textnaut, the same engine in a text terminal.
layout: hub.njk
---

<p class="hub-crumbs"><a href="{{ '/web/hub/' | url }}">Hub</a> › Web platform</p>

# Web platform

<p class="warning"><strong>⚠️ EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.</strong> This covers the web rendering engine, the browser and every page script they run.</p>

Foafnaut is a web browser with its own built-in engine, BubblePopKit. The engine parses
HTML, computes CSS, lays out text and boxes, runs page scripts with BubblePopJS and draws
with WebGPU. Textnaut is the same engine in a text terminal. The pages below are about both.

## Pages

<ul class="post-series">
  <li><a href="{{ '/web/hub/foafnaut/' | url }}">Foafnaut</a> — the browser in a page: tabs, an address bar for URLs, searches and commands, view source, XML with XSLT, drawn by the built-in engine with WebGPU. It works at phone width.</li>
  <li><a href="{{ '/web/hub/textnaut/' | url }}">Textnaut</a> — the text-mode browser in a page: the engine lays out a page and Textnaut shows it as a grid of characters with numbered links. The terminal program: <code>npx @foafos/textnaut</code>.</li>
  <li><a href="{{ '/web/hub/foafnaut/pages/start.html' | url }}">Start page</a> — sites on the web to try, grouped, with a note on how well each works today, and Hub copies of openly licensed pages that open inside Foafnaut.</li>
  <li><a href="{{ '/web/hub/foafnaut/pages/index.html' | url }}">Demo pages</a> — what the engine draws, by kind: scripts, WebGPU and WebGL, SVG, text, XML and XSLT.</li>
  <li><a href="{{ '/web/hub/foafnaut/pages/stress.html' | url }}">Stress tests</a> — heavy pages kept apart, with what makes each one heavy.</li>
  <li><a href="{{ '/web/hub/foafnaut/pages/settings.html' | url }}">Settings</a> — the page script engine, text size, theme and the other choices (the gear in Foafnaut's toolbar, or <code>:settings</code>).</li>
  <li><a href="{{ '/web/hub/notebook/' | url }}">Notebook: cells drawn by the built-in engine</a> — a page in a canvas, a Foafnaut view with scripts, and Textnaut's text, from one engine, with each cell's timings.</li>
  <li><a href="{{ '/web/hub/conformance/' | url }}">Conformance</a> — Test262 and the Web Platform Tests from full measured runs, next to other browsers, with the history of every run.</li>
  <li><a href="{{ '/web/hub/specs/' | url }}">Data and documents conformance</a> — the W3C data and document standards (RDF, SPARQL, OWL 2, SHACL, XML, XSLT and more) the same code passes, suite by suite.</li>
  <li><a href="./foafnaut/notes/">Foafnaut notes</a> — short dated notes on what the browser can do, newest first, with links that open each demo in Foafnaut. The same notes make its Atom feed.</li>
  <li><a href="./foafnaut/">About Foafnaut</a> — what the browser is, where to start, and the latest notes.</li>
  <li><a href="{{ '/web/hub/foafnaut2525-status/' | url }}">Project status</a> — where the engine stands, suite by suite; the engine renders this note too.</li>
  <li><a href="{{ '/web/hub/html-webgpu/' | url }}">HTML and CSS in the built-in engine</a> — editable HTML/CSS, block and inline layout, shared vector geometry, WebGPU pixels and clickable source-mapped links.</li>
  <li><a href="{{ '/web/hub/render-scores/' | url }}">Rendering and font scores</a> — the score of each rendering and font suite by commit, and the largest failure groups: the next fixes.</li>
  <li><a href="{{ '/web/hub/render-scores/' | url }}#svg-tiny-pixels">SVG Tiny 1.2 test suite results</a> — each W3C SVG Tiny 1.2 test drawn by the engine with WebGPU and compared with its reference image.</li>
</ul>
