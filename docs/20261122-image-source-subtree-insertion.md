# Start images when a cloned subtree is connected

The pinned natural-dimensions fixture clones a fragment with authored image
sources and inserts it into the document while parsing. Cloning copies the
attributes in the DOM arena, so the JavaScript attribute observer never sees
those writes. The initial image scan also predates those cloned nodes.

Track images in cloned or parsed subtrees. After a successful fragment or node
insertion connects the subtree, schedule each tracked image with the existing
update task. Include eager images in the main document load delay while the
document is loading. Keep disconnected fragments and template contents inert
and let the existing lazy observer govern lazy requests.

The source-extracted Node suite checks that a detached fragment stays idle,
that connecting its contents schedules both eager and lazy image updates,
that only the eager image holds the load event, and that moving the contents
again does not reschedule them. Run the pinned image and adjacent flexbox
WPT fixtures with the native engine to check end-to-end behavior.
