# Draft: modularising Factoidal and the browser together

Status: draft for discussion, 5 November 2026. Nothing here is decided.

Owner, 2026-11-05, verbatim: "keep everything in a common framework for now rather than
splitting into TWO and just TWO. We will need all kinds of modularizations [...] I don't want
them all in the Factoidal core NPM module, but most of the pure standards bits can be. Then we
can modularize 'core' in a careful way. Only pure browser stuff (software UI, logo, bookarking
menu system etc etc.) need to be radically separate. If it is a web standards implementation it
goes into Factoidal and ... html and css sit as close to rdf as xml, so we will modularize
everything together soon."

## The finding that shapes this

Measured from `import` lines on `main`: 1,468 Lean files, 582,663 lines.

By directory, the corpus is one tangle. From `HTML`, `XML`, `RDF`, `Syntax` or `SPARQL` you
reach 56 areas and about 532,000 lines. By file, the closures are small:

| Root module | Files | Lines |
|---|---|---|
| `XML.Parser` | 2 | 4,677 |
| `HTML.TreeBuilder` | 4 | 2,697 |
| `DOM.OfHtml` | 7 | 4,190 |
| `Rendering.Style` | 11 | 5,130 |
| `Rendering.Layout` | 18 | 6,966 |
| `Rendering.SfntShape` | 16 | 3,704 |
| `Syntax.NTriples` | 6 | 3,781 |
| `Syntax.Turtle` | 10 | 7,256 |
| `Rendering.RdfView` (HTML and RDF together) | 14 | 8,061 |
| `JSONLD.ToRdf` | 15 | 11,321 |
| `XSLT.Transform` | 15 | 10,689 |
| `XMPP.Server` | 20 | 12,620 |
| `XSLT4.Transform` | 128 | 66,929 |

So the modules already exist in the file graph. Directories are not the module boundary. A few
bridge and test files make the directory cycle, for example `XML.DSig` to `Crypto` and `VC`,
`XML.DSigXslt` to `XSLT4`, `RDF.Sink` to the serialisers, `RDF.SinkJsonLd` to `JSONLD`, and
`XSD.InteropTests` to six areas. `build-web-render.sh` already uses this: it builds a short root
list, not the library.

## Proposal: one framework, many profiles

Keep one repository and one Lean package. Add **profiles**: named lists of root modules. A profile
is what we build, test, size and ship. Profiles overlap freely, so this is not a split.

| Profile | Contents | Used by |
|---|---|---|
| `text` | Unicode, Encoding, Regex, Text, JSON, WHATWG URL and IDNA, IRI | everything |
| `markup` | XML, HTML, DOM, namespaces, XPath | browser, RDF/XML, XSLT |
| `style` | CSS, layout, fonts and shaping, SVG, MathML, scene, Selection, session history | browser, documents |
| `rdf` | RDF core, Turtle family, RDF/XML, JSON-LD | core |
| `query` | SPARQL, SHACL, ShEx, RDFS | core |
| `transform` | XSLT, XPath 4, XQuery | core, browser |
| `net` | HTTP, XMPP, LWS, Solid, WebDAV, JOSE, Crypto | servers, clients |
| `store` | Storage, Qlvr, HDT, Cottas | servers |
| `reason` | OWL, RIF, CL, Planner | optional |
| `embedded` | `text`, part of `markup` and `style`, N-Triples: a device target, with a size limit | ESP32-P4 |

HTML, CSS and RDF sit beside XML here, as you said. `Rendering.RdfView` shows why a two-way split
would be wrong: it needs both sides, in 8,061 lines.

## What moves, and what stays out

**Into `L4Factoidal`, because they implement standards:** `SVG*`, `Graphics`, `GraphicsPrepared`,
`SceneSVG`, `Font`, `RenderPlan`, `WebRender*`, `WebDocument`, `WebSelection`, `WebHistory` (HTML
session history), `WebXslt`. Their tests move with them. About 5,000 lines.

**Radically separate:** the browser product: software UI, logo, bookmarks, menus, tabs, the
`foafnaut` command, native window hosts. Also the demo applications: `FoafNaut`, `FoafPresentation`,
`FoafLiveBridge`, `Solving*`, `Demos`. These may import Factoidal; Factoidal never imports them.

**To decide:** `UI.lean` and `L4Factoidal.UI.*`, which mix a generic event and effect model with
application policy.

## npm

- `@factoidal/core` stays the main package, built from `text`, `markup`, `rdf`, `query` and what
  it already ships. Today its API does not change.
- Large profiles become separate wasm assets, loaded on request, or sibling packages. Which of
  these is an open question.
- The browser engine is a consumer. `style` need not load for a user who only wants RDF.

## Gates that make this hold

1. A profile file lists roots. A tool reports files, lines, wasm bytes and engine start cost for
   each profile, and fails on an unplanned increase. `web-render/check-budget.mjs` is the small
   version of this.
2. A rule per profile for forbidden imports, for example `markup` must not reach `Crypto`.
3. Tests do not count towards a closure. Move them to separate roots.

## Order of work

1. Add the profile lists and the report tool, with no file moves. Low risk, useful at once.
2. Cut the bridge files: `XML.DSig*` out of the `markup` closure, `RDF.Sink*` split from RDF core.
3. Move the standards files from `labs/demos/foafnaut` when session `depmap-9b` is at a clean point.
4. Split npm assets by profile.
5. Add `embedded` and build it for rv32.

## Open questions

1. Separate wasm assets in one npm package, or sibling npm packages?
2. Does `style` belong in `@factoidal/core` at all, or in a sibling such as `@factoidal/web`?
3. Do directories get renamed to match profiles, or do profile lists stay the only truth? I suggest
   no renames for now: they cost much and the file graph already gives the answer.
4. Where does the browser product live: `labs/`, a top-level `apps/`, or its own repository?
5. Does QuickJS, or a later JS engine, count as a profile or a host capability?
