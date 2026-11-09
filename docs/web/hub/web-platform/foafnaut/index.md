---
title: Foafnaut
description: Foafnaut, the web browser built on foafnaut2525, the web rendering engine written in Lean; the latest notes and where to start.
layout: hub.njk
---

<p class="hub-crumbs"><a href="{{ '/web/hub/' | url }}">Hub</a> › <a href="{{ '/web/hub/web-platform/' | url }}">Web platform</a> › Foafnaut</p>

# Foafnaut

Foafnaut is a web browser built on foafnaut2525, a web rendering engine written in
Lean. The engine parses HTML, computes CSS, lays out text and boxes, and draws with
WebGPU. It runs in a web page, in its own macOS window, and as a sandboxed guest. Real
sites mostly do not load yet.

- [Open Foafnaut]({{ '/web/hub/foafnaut/' | url }}): the browser in this site, with
  tabs and an address bar. It works at phone width.
- [The demo pages]({{ '/web/hub/foafnaut/?page=index.html' | url }}), and
  [JavaScript in Foafnaut]({{ '/web/hub/foafnaut/?page=js-status.html' | url }}), the
  status of page scripts.
- [foafnaut2525 project status]({{ '/web/hub/foafnaut2525-status/' | url }}) and
  [Rendering and font scores]({{ '/web/hub/render-scores/' | url }}).

## Latest notes

<ul class="post-series">
{%- for note in collections.foafnautNotes.slice().reverse().slice(0, 5) %}
  <li><a href="{{ note.url | url }}">{{ note.data.titleHtml | safe }}</a> — <time datetime="{{ note.date.toISOString() }}">{{ note.date.toLocaleDateString("en-GB", { "day": "numeric", "month": "long", "year": "numeric", "timeZone": "UTC" }) }}</time>. {{ note.data.summaryHtml | safe }}</li>
{%- endfor %}
</ul>

[All Foafnaut notes]({{ '/web/hub/web-platform/foafnaut/notes/' | url }}) ·
[the notes as a feed, in Foafnaut]({{ '/web/hub/foafnaut/?page=feed.xml' | url }})
