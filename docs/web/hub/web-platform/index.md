---
title: Web platform
description: The Hub pages about foafnaut2525, the web rendering engine written in Lean, and Foafnaut, the browser built on it.
layout: hub.njk
---

<p class="hub-crumbs"><a href="{{ '/web/hub/' | url }}">Hub</a> › Web platform</p>

# Web platform

<p class="warning"><strong>⚠️ EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.</strong> This covers the web rendering engine, the browser and every page script they run.</p>

foafnaut2525 is a web rendering engine written in Lean. It parses HTML, computes CSS,
lays out text and boxes, and draws with WebGPU. Foafnaut is the browser built on it.
The pages below are about both.

## Pages

<ul class="post-series">
  <li><a href="{{ '/web/hub/foafnaut/' | url }}">Foafnaut</a> — the Lean browser in a page: tabs, an address bar for URLs, searches and commands, view source, XML with XSLT, drawn with WebGPU. It works at phone width.</li>
  <li><a href="./foafnaut/notes/">Foafnaut notes</a> — short dated notes on what the browser can do, newest first, with links that open each demo in Foafnaut. The same notes make its Atom feed.</li>
  <li><a href="./foafnaut/okrs/">Objectives and key results</a> — four objectives of equal weight (standards, security, privacy, performance) and the milestones on the way to 90% of the Web Platform Tests.</li>
  <li><a href="./foafnaut/">About Foafnaut</a> — what the browser is, where to start, and the latest notes.</li>
  <li><a href="{{ '/web/hub/foafnaut2525-status/' | url }}">foafnaut2525 project status</a> — where the Lean web rendering engine stands, suite by suite; the engine renders this note too.</li>
  <li><a href="{{ '/web/hub/html-webgpu/' | url }}">HTML and CSS in Lean</a> — editable HTML/CSS, Lean block and inline layout, shared vector geometry, WebGPU pixels and clickable source-mapped links.</li>
  <li><a href="{{ '/web/hub/render-scores/' | url }}">Rendering and font scores</a> — the score of each rendering and font suite by commit, and the largest failure groups: the next fixes.</li>
  <li><a href="{{ '/web/hub/render-scores/' | url }}#svg-tiny-pixels">SVG Tiny 1.2 test suite results</a> — each W3C SVG Tiny 1.2 test drawn by the Lean engine with WebGPU and compared with its reference image.</li>
</ul>
