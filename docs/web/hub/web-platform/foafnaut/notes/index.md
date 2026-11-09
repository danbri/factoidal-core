---
title: Foafnaut notes
description: Short dated notes on what the Foafnaut browser can do, newest first, with links that open each demo in Foafnaut.
layout: hub.njk
---

<p class="hub-crumbs"><a href="{{ '/web/hub/' | url }}">Hub</a> › <a href="{{ '/web/hub/web-platform/' | url }}">Web platform</a> › <a href="{{ '/web/hub/web-platform/foafnaut/' | url }}">Foafnaut</a> › Notes</p>

# Foafnaut notes

Short dated notes on what the [Foafnaut]({{ '/web/hub/foafnaut/' | url }}) browser can
do, newest first. Each note says what works now, gives a number or two with the
record it comes from, and links the demo pages that show it. An "Open in Foafnaut"
link opens that page in the browser on this site.

The same notes make the Atom feed that Foafnaut draws with XSLT:
[open the feed in Foafnaut]({{ '/web/hub/foafnaut/?page=feed.xml' | url }}), or read
[feed.xml]({{ '/web/hub/foafnaut/pages/feed.xml' | url }}) itself.

<ul class="post-series">
{%- for note in collections.foafnautNotes.slice().reverse() %}
  <li><a href="{{ note.url | url }}">{{ note.data.titleHtml | safe }}</a> — <time datetime="{{ note.date.toISOString() }}">{{ note.date.toLocaleDateString("en-GB", { "day": "numeric", "month": "long", "year": "numeric", "timeZone": "UTC" }) }}</time>. {{ note.data.summaryHtml | safe }}{% for demo in note.data.demos %} Open in Foafnaut: <a href="{{ ('/web/hub/foafnaut/?page=' + demo) | url }}">{{ foafnautPages[demo].html | safe }}</a>.{% endfor %}</li>
{%- endfor %}
</ul>

## Writing a note

A note is one Markdown file in `docs/web/hub/web-platform/foafnaut/notes/posts/`. Its
front matter gives `title`, `date` (UTC, `2026-11-09T08:34:22Z`), `category`, `commit`,
`summary` and, if it has demos, `demos` (names of pages in
`labs/demos/foafnaut/pages/`). `tools/build-demo-pages.py` then writes `feed.xml` from
the notes. `docs/web/hub/README.md` has the details.
