# How foafnaut is built

Every part below is one file or a few. Links to GitHub open in your system browser, because this engine can not draw GitHub yet.

## Parsing

- [Tokenizer.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/HTML/Tokenizer.lean): HTML tokenizer
- [TreeBuilder.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/HTML/TreeBuilder.lean): HTML tree construction
- [Parser.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/XML/Parser.lean): XML parser
- [NamespaceView.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/XML/NamespaceView.lean): XML namespaces
- [Arena.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/DOM/Arena.lean): the DOM

## Style and layout

- [Style.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/Style.lean): CSS selectors and computed style
- [Layout.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/Layout.lean): block and inline layout
- [Links.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/Links.lean): link regions
- [Scene.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/Scene.lean): the common scene

## Fonts and text

- [Font.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/Font.lean): the bitmap font
- [LeanFontShape.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/LeanFontShape.lean): the Lean text shaper
- [SfntShape.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/SfntShape.lean): OpenType shaping
- [SfntGpos.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/SfntGpos.lean): OpenType positioning
- [FontPolicy.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/FontPolicy.lean): font trust and safety

## SVG

- [SVG.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVG.lean): the strict reader, and the WGSL shader
- [SVGForgiving.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGForgiving.lean): draw what can be drawn, and SVG fonts
- [SVGPath.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGPath.lean): paths
- [SVGCurves.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGCurves.lean): curves
- [SVGStroke.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGStroke.lean): strokes
- [SVGDash.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGDash.lean): dashes
- [SVGCSS.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGCSS.lean): SVG style sheets
- [SVGReferences.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGReferences.lean): references and use

## Transforming documents

- [WebXslt.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/WebXslt.lean): XML pages with xml-stylesheet
- [Transform.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/XSLT/Transform.lean): XSLT 1.0
- [Interp.lean](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/XSLT4/Interp.lean): XSLT 3.0 and 4.0

## The browser

- [WebDocument.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/WebDocument.lean): one page, from source to frame
- [WebRender.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/WebRender.lean): HTML and embedded SVG to a scene
- [WebShell.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/WebShell.lean): tabs, address bar and buttons
- [WebHistory.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/WebHistory.lean): session history and keys
- [WebSelection.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/WebSelection.lean): selection, copy and zoom

## GPU

- [RenderPlan.lean](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/RenderPlan.lean): WebGPU commands, chosen in Lean
- [render_plan.ts](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/render_plan.ts): runs those commands
- [gpu_transport.ts](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/gpu_transport.ts): offscreen sessions

## Host, not Lean

- [run_html.ts](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/run_html.ts): the event loop
- [native_window.m](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/native_window.m): the Cocoa window
- [native_html_document.ts](https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/native_html_document.ts): fetches bytes
